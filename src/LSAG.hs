module LSAG
( sign
, verify
, genNPubKeys
) where

import           Control.Monad.State
import           Crypto.Hash
import           Crypto.Number.Serialize      (os2ip)
import           Crypto.Number.Generate       (generateBetween)
import qualified Crypto.PubKey.ECC.Generate   as ECC
import qualified Crypto.PubKey.ECC.Prim       as ECC
import qualified Crypto.PubKey.ECC.Types      as ECC
import qualified Crypto.PubKey.ECC.ECDSA      as ECDSA
import           Crypto.Random.Types          (MonadRandom)
import qualified Data.ByteArray               as BA
import qualified Data.ByteString              as BS
import           Data.Monoid
import           Data.List                    hiding (insert)
import           Protolude                    hiding (hash, head)

-- | Sign message
sign
  :: MonadRandom m
  => [ECDSA.PublicKey]                    -- ^ List of public keys
  -> (ECDSA.PublicKey, ECDSA.PrivateKey)  -- ^ Signer's public and private keys
  -> Int                                  -- ^ Signer's position in list of public keys
  -> ByteString                           -- ^ Message
  -> m (Integer, [Integer], ECC.Point)
sign pubKeys (pubKey, privKey) k msg = do
  -- Generate L random s values
  -- (sk + 1) : [sk + 2, ..., s0, 1, ..., sk - 1]
  (sK1:sK2ToPrevSK) <- replicateM (participants - 1) $ generateBetween 1 (n - 1)

  -- Pick u and compute challenge c = H(L, y, m, [u] * g, [u] * h)
  u <- generateBetween 1 (n - 1)
  -- Initial challenge at k + 1
  -- H(L, y, m, [u] * g, [u] * h)
  let chK1 = genChallenge curve pubKeys y msg (gu u) (hu u)

  -- Generate challenges
  -- [ck, ..., c1, c0, ... ck + 2, ck + 1]
  let reversedChKToChK1 = runChallenges sK1 chK1 sK2ToPrevSK u y h
      chK = head reversedChKToChK1

  -- Compute s = u - x * c mod n
  let sK = (u - ECDSA.private_d privKey * chK) `mod` n

  -- Reverse reversedChKToChK1: [chK + 1, ck + 2, ..., 0, 1, ..., chK]
  -- Ordered challenges: [c0, c1, ..., cn-1]
  let orderedChallenges = orderChallenges (reverse reversedChKToChK1)

  -- Ordered ss: [s0, s1, ..., sk, ..., sn-1]
  -- (sK : sK1 : sK2ToPrevSK): [sk, sk + 1, ..., sk - 1]
  let orderedSS = orderSS (sK : sK1 : sK2ToPrevSK)
      ch0 = head orderedChallenges

  -- The signature is (ch0, (s0, ..., sn-1), y)
  pure (ch0, orderedSS, y)

  where
    curve = ECDSA.public_curve pubKey
    -- h = [Hash(L)] * g
    h = ECC.pointBaseMul curve (hashPubKeys curve pubKeys)
    -- y = [x] * h
    y = ECC.pointMul curve (ECDSA.private_d privKey) h
    n = ECC.ecc_n (ECC.common_curve curve)
    g = ECC.ecc_g (ECC.common_curve curve)
    gu u = ECC.pointMul curve u g
    hu u = ECC.pointMul curve u h
    participants = length pubKeys
    runChallenges sK1 chK1 sK2ToPrevSK u y h = evalState
      (genChallenges curve pubKeys y msg sK2ToPrevSK)
      (initState sK1 chK1)
    initState sK1 chK1 =
      (((k + 1) `mod` participants, sK1, chK1), [chK1])
    orderChallenges ch =
      drop (participants - (k + 1)) ch <>
      take (participants - (k + 1)) ch
    orderSS sKToPrevSK =
      drop (participants - k) sKToPrevSK <>
      take (participants - k) sKToPrevSK

verify
  :: [ECDSA.PublicKey]                    -- ^ List of participants public keys
  -> (Integer, [Integer], ECC.Point)      -- ^ Signature
  -> ByteString                           -- ^ Message
  -> Bool
verify pubKeys (ch0, [], y) msg = panic "Invalid input"
verify pubKeys (ch0, [s], y) msg = panic "Invalid input"
verify pubKeys (ch0, s0:s1:s2ToEnd, y) msg = ch0 == ch0'
  where
    -- We assume for now that all curves are the same
    curve = ECDSA.public_curve $ head pubKeys
    -- In ECC, h is a point in the curve. h = g x H_2(L)
    -- Compute y = h x x_pi
    h = ECC.pointBaseMul curve (hashPubKeys curve pubKeys)
    y0 = ECDSA.public_q $ head pubKeys
    -- z0' = [s0] * g + [ch0] * y0
    z0' = ECC.pointAdd curve
      (ECC.pointMul curve s0 g)
      (ECC.pointMul curve ch0 y0)
    -- z0'' = [s0] * h + [c0] * y
    z0'' = ECC.pointAdd curve
      (ECC.pointMul curve s0 h)
      (ECC.pointMul curve ch0 y)
    g = ECC.ecc_g (ECC.common_curve curve)
    participants = length pubKeys

    -- initial challenge - ch1
    ch1 = genChallenge curve pubKeys y msg z0' z0''
    -- [ch0, chN-1 ..., ch2, ch1]
    challenges = evalState
      (genChallenges curve pubKeys y msg s2ToEnd)
      ((1 `mod` participants, s1, ch1), [ch1])
    ch0' = head challenges

genChallenges
  :: ECC.Curve
  -> [ECDSA.PublicKey]  -- ^ List of public keys L
  -> ECC.Point          -- ^ y = h x [x]
  -> BS.ByteString      -- ^ message msg
  -> [Integer]          -- ^ random ss
  -> State ((Int, Integer, Integer), [Integer]) [Integer]
genChallenges curve pubKeys y msg ss = do
  ((prevK, prevS, prevCh), challenges) <- get
  let ch = challenge prevK prevS prevCh
  case ss of
    [] -> pure $ ch : challenges
    (s:ss) -> do
      put (((prevK + 1) `mod` participants, s, ch)
          , ch : challenges
          )
      genChallenges curve pubKeys y msg ss
  where
    g = ECC.ecc_g (ECC.common_curve curve)
    h = ECC.pointBaseMul curve (hashPubKeys curve pubKeys)
    gs prevK prevS prevCh =
      ECC.pointAdd curve
        (ECC.pointMul curve prevS g)
        (ECC.pointMul curve prevCh (ECDSA.public_q $ pubKeys !! prevK))
    hs prevK prevS prevCh =
      ECC.pointAdd curve
        (ECC.pointMul curve prevS h)
        (ECC.pointMul curve prevCh y)
    challenge prevK prevS prevCh =
      genChallenge curve pubKeys y msg
        (gs prevK prevS prevCh)
        (hs prevK prevS prevCh)
    participants = length pubKeys

-- | Generate challenge from a given message
--
-- @c = H(L, y, m, p1, p2)@
genChallenge
  :: ECC.Curve
  -> [ECDSA.PublicKey]  -- ^ List of public keys L
  -> ECC.Point          -- ^ y = [privKey] * h
  -> BS.ByteString      -- ^ message msg
  -> ECC.Point          -- ^ generator g
  -> ECC.Point          -- ^ h = [H(L)] * g
  -> Integer
genChallenge c pubKeys y msg g h =
  oracle c (pubKeys' <> y' <> msg <> g' <> h')
  where
    pubKeys' = pubKeysToBS pubKeys
    y' = pointToBS y
    g' = pointToBS g
    h' = pointToBS h

-- | Generate N different public keys. @L = {y1, ..., yn}@
genNPubKeys :: MonadRandom m => ECC.Curve -> Int -> m [ECDSA.PublicKey]
genNPubKeys curve n = replicateM n (fst <$> ECC.generate curve)

-- | Convert point to bytestring
pointToBS :: ECC.Point -> BS.ByteString
pointToBS ECC.PointO      = ""
pointToBS (ECC.Point x y) = show x <> show y

-- | Convert list of public keys to bytestring
pubKeysToBS :: [ECDSA.PublicKey] -> BS.ByteString
pubKeysToBS = foldMap (pointToBS . ECDSA.public_q)

-- | Hash list of public keys
hashPubKeys :: ECC.Curve -> [ECDSA.PublicKey] -> Integer
hashPubKeys c = oracle c . pubKeysToBS

-- | Unpredictable but deterministic random response
oracle :: ECC.Curve -> BS.ByteString -> Integer
oracle curve x = os2ip (sha256 x) `mod` n
  where
    n = ECC.ecc_n (ECC.common_curve curve)

sha256 :: BS.ByteString -> BS.ByteString
sha256 bs = BA.convert (hash bs :: Digest SHA3_256)
