-- | Implementation of Linkable Spontaneus Anonymous Group (LSAG) Signature over elliptic curve cryptography.
--
-- >>> (pubKey, privKey) <- ECC.generate curve -- Generate public and private keys
-- >>> extPubKeys <- genNPubKeys curve nParticipants -- Generate random foreign participants
-- >>> k <- fromInteger <$> generateBetween 0 (toInteger $ length extPubKeys - 1) -- Position of the signer's key in the public keys list (k)
-- >>> let pubKeys = insert k pubKey extPubKeys -- Insert signer's public key into the list of public keys
-- >>> signature <- sign pubKeys (pubKey, privKey) msg -- Sign message with list of public keys and signer's key pair
-- >>> verify pubKeys signature msg -- Verify signature
-- True

module LSAG
( sign
, verify
, genNPubKeys
) where

import           Control.Monad.State
import           Control.Monad.Fail
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
import           Data.List
import           Protolude                    hiding (hash, head)
import Math.NumberTheory.Moduli.Sqrt (sqrtModP)

-- | Generates a ring signature for a message given a specific set of
-- public keys and a signing key belonging to one of the public keys
-- in the set
--
-- It returns a signature (c0, ss, y) :
--
-- * c0: Initial value to reconstruct signature.
-- * ss: vector of randomly generated values with encrypted secret to
-- reconstruct signature {s0 ... sn-1}.
-- * y: Link for current signer.
sign
  :: (MonadRandom m, MonadFail m)
  => [ECDSA.PublicKey]                    -- ^ List of public keys
  -> (ECDSA.PublicKey, ECDSA.PrivateKey)  -- ^ Signer's public and private keys
  -> ByteString                           -- ^ Message
  -> m (Integer, [Integer], ECC.Point)
sign pubKeys (pubKey, privKey) msg =
  case pubKey `elemIndex` pubKeys of
    Nothing -> panic "Signer's public key is not among public keys"
    Just k -> do
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
      let reversedChKToChK1 = runChallenges k sK1 chK1 sK2ToPrevSK u y h
          chK = head reversedChKToChK1

      -- Compute s = u - x * c mod n
      let sK = (u - ECDSA.private_d privKey * chK) `mod` n

      -- Reverse reversedChKToChK1: [chK + 1, ck + 2, ..., 0, 1, ..., chK]
      -- Ordered challenges: [c0, c1, ..., cn-1]
      let orderedChallenges = orderChallenges k (reverse reversedChKToChK1)

      -- Ordered ss: [s0, s1, ..., sk, ..., sn-1]
      -- (sK : sK1 : sK2ToPrevSK): [sk, sk + 1, ..., sk - 1]
      let orderedSS = orderSS k (sK : sK1 : sK2ToPrevSK)
          ch0 = head orderedChallenges

      -- The signature is (ch0, (s0, ..., sn-1), y)
      pure (ch0, orderedSS, y)

  where
    curve = ECDSA.public_curve pubKey
    -- h = [Hash(L)]
    h = generateH g curve (show $ hashPubKeys curve pubKeys)
    -- y = [x] * h
    y = ECC.pointMul curve (ECDSA.private_d privKey) h
    n = ECC.ecc_n (ECC.common_curve curve)
    g = ECC.ecc_g (ECC.common_curve curve)
    gu u = ECC.pointMul curve u g
    hu u = ECC.pointMul curve u h
    participants = length pubKeys
    runChallenges k sK1 chK1 sK2ToPrevSK u y h = evalState
      (genChallenges pubKeys y msg sK2ToPrevSK)
      (initState k sK1 chK1)
    initState k sK1 chK1 =
      (((k + 1) `mod` participants, sK1, chK1), [chK1])
    orderChallenges k ch =
      drop (participants - (k + 1)) ch <>
      take (participants - (k + 1)) ch
    orderSS k sKToPrevSK =
      drop (participants - k) sKToPrevSK <>
      take (participants - k) sKToPrevSK

-- | Verify if a valid signature was made by any public key in the set of public keys L.
--
-- Return a boolean value indicating if signature is valid.
verify
  :: [ECDSA.PublicKey]                    -- ^ List of participants public keys
  -> (Integer, [Integer], ECC.Point)      -- ^ Signature
  -> ByteString                           -- ^ Message
  -> Bool
verify pubKeys (ch0, [], y) msg = panic "Invalid input"
verify pubKeys (ch0, [s], y) msg = panic "Invalid input"
verify pubKeys (ch0, s0:s1:s2ToEnd, y) msg = ch0 == ch0'
  where
    curve0 = ECDSA.public_curve $ head pubKeys
    -- h = [H(L)]
    h = generateH g curve0 (show $ hashPubKeys curve0 pubKeys)

    -- h = ECC.pointBaseMul curve0 (hashPubKeys curve0 pubKeys)
    y0 = ECDSA.public_q $ head pubKeys
    -- z0' = [s0] * g + [ch0] * y0
    z0' = ECC.pointAdd curve0
      (ECC.pointMul curve0 s0 g)
      (ECC.pointMul curve0 ch0 y0)
    -- z0'' = [s0] * h + [c0] * y
    z0'' = ECC.pointAdd curve0
      (ECC.pointMul curve0 s0 h)
      (ECC.pointMul curve0 ch0 y)
    g = ECC.ecc_g (ECC.common_curve curve0)
    participants = length pubKeys

    -- initial challenge - ch1
    ch1 = genChallenge curve0 pubKeys y msg z0' z0''
    -- [ch0, chN-1 ..., ch2, ch1]
    challenges = evalState
      (genChallenges pubKeys y msg s2ToEnd)
      ((1 `mod` participants, s1, ch1), [ch1])
    ch0' = head challenges

genChallenges
  :: [ECDSA.PublicKey]  -- ^ List of public keys L
  -> ECC.Point          -- ^ y = h x [x]
  -> BS.ByteString      -- ^ message msg
  -> [Integer]          -- ^ random ss
  -> State ((Int, Integer, Integer), [Integer]) [Integer]
genChallenges pubKeys y msg ss = do
  ((prevK, prevS, prevCh), challenges) <- get
  let curve = ECDSA.public_curve $ pubKeys !! prevK
  let ch = challenge curve prevK prevS prevCh
  case ss of
    [] -> pure $ ch : challenges
    (s:ss) -> do
      put (((prevK + 1) `mod` participants, s, ch)
          , ch : challenges
          )
      genChallenges pubKeys y msg ss
  where
    g curve = ECC.ecc_g (ECC.common_curve curve)
    h curve = generateH (g curve) curve (show $ hashPubKeys curve pubKeys)
    gs curve prevK prevS prevCh =
      ECC.pointAdd curve
        (ECC.pointMul curve prevS (g curve))
        (ECC.pointMul curve prevCh (ECDSA.public_q $ pubKeys !! prevK))
    hs curve prevK prevS prevCh =
      ECC.pointAdd curve
        (ECC.pointMul curve prevS (h curve))
        (ECC.pointMul curve prevCh y)
    challenge curve prevK prevS prevCh =
      genChallenge curve pubKeys y msg
        (gs curve prevK prevS prevCh)
        (hs curve prevK prevS prevCh)
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


-- | Iterative algorithm to generate H.
-- The important to hide its discrete logarithm "k" such that H = kG
generateH :: ECC.Point -> ECC.Curve -> [Char] -> ECC.Point
generateH g curve extra =
  case yM of
    Nothing -> generateH g curve (toS $ '1':extra)
    Just y -> if ECC.isPointValid curve (ECC.Point x y)
      then ECC.Point x y
      else generateH g curve (toS $ '1':extra)
  where
    x = oracle curve (pointToBS g <> toS extra) `mod` p
    yM = sqrtModP (x ^ 3 + 7) p
    p = ECC.ecc_p cp
      where
        cp = case curve of
               ECC.CurveFP c -> c
               ECC.CurveF2m _ -> panic "Not a FP curve"

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
