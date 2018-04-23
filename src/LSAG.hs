module LSAG where

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
import           Data.List
import           Protolude                    hiding (hash, head)

secp256k1Curve :: ECC.Curve
secp256k1Curve = ECC.getCurveByName ECC.SEC_p256k1

testSignature
  :: ECC.Curve
  -> Int
  -> ByteString
  -> IO Bool
testSignature curve nParticipants msg = do
  -- Gen public and private keys
  (pubKey, privKey) <- ECC.generate curve
  extPubKeys <- genNPubKeys curve nParticipants
  -- k = position of the signer's key in the list of public keys
  k <- fromInteger <$> generateBetween 1 (toInteger $ length extPubKeys - 1)
  -- let k = 2
  let pubKeys = insertPubKey k pubKey extPubKeys
  signature <- sign pubKeys (pubKey, privKey) k msg
  -- print "-------------------- Signature ----------------------"
  -- print signature
  verify pubKeys signature msg

sign
  :: [ECDSA.PublicKey]                    -- ^ List of public keys
  -> (ECDSA.PublicKey, ECDSA.PrivateKey)  -- ^ Signer's public and private keys
  -> Int                                  -- ^ Signer's position in list L
  -> ByteString                           -- ^ Message
  -> IO (Integer, [Integer], ECC.Point)
sign pubKeys (pubKey, privKey) k msg = do
  -- print "---------- Signature h -------------"
  -- print h
  -- Generate L random s values
  -- (sk + 1) : [sk + 2, ..., sn, 1, ..., sk - 1]
  (sK1:sK2ToPrevSK) <- replicateM (participants - 1) $ generateBetween 1 (n - 1)
  -- let (sK1:sK2ToPrevSK) = fmap toInteger [1..(participants - 1)]
  -- print "-------------- s -------------------"
  -- print sK1
  -- print "-------------- ss -------------------"
  -- print sK2ToPrevSK

  --------------------- STEP 2 -----------------------
  -- Pick u and compute challenge c = H(L, y, m, g^u, h^u)
  -- Initial challenge on k + 1
  u <- generateBetween 1 (n - 1)
  -- print "-------------- u -------------------"
  -- print u

  --------------------- STEP 3 -----------------------
  -- Generate challenges
  -- Challenges start at (k + 1)
  -- [ck, ..., 1, cn, ... ck + 2, ck + 1]
  let reversedChKToChK1 = runChallenges sK1 sK2ToPrevSK u y h
      chK = head reversedChKToChK1

  --------------------- STEP 4 -----------------------
  -- Compute s = u - x * c mod q
  let sK = (u - ECDSA.private_d privKey * chK) `mod` n

  -- Reverse reversedChKToChK1: [chK + 1, ck + 2, ..., n, 1, ..., chK]
  -- Ordered challenges: [c1, c2, ..., cn]
  let orderedChallenges = orderChallenges (reverse reversedChKToChK1)

  -- Ordered ss: [s1, s2, ..., sk, ..., sn]
  -- (sK : sK1 : sK2ToPrevSK): [sk, sk + 1, ..., sk - 1]
  let orderedSS = orderSS (sK : sK1 : sK2ToPrevSK)

  -- The signature is (c1, (s1, ..., sn), y)
  let ch1 = head orderedChallenges
  print "-------------------- k -----------------------"
  print k
  -- print "----------------- reversedChKToChK1 -----------------"
  -- print reversedChKToChK1
  print "----------------- Ordered Challenges - ch1ToChN -----------------"
  print orderedChallenges
  -- print "----------------- Ordered SS - s1ToSN -----------------"
  -- print orderedSS

  pure (ch1, orderedSS, y)

  where
    curve = ECDSA.public_curve pubKey
    -- h = [Hash(L)] * g
    h = ECC.pointBaseMul curve (hashPubKeys curve pubKeys)
    -- y = [x] * h
    y = ECC.pointMul curve (ECDSA.private_d privKey) h
    n = ECC.ecc_n (ECC.common_curve curve)
    g = ECC.ecc_g (ECC.common_curve curve)
    gu u = ECC.pointMul curve u g
    hu u = ECC.pointMul curve u g
    participants = length pubKeys
    runChallenges sK1 sK2ToPrevSK u y h = evalState
      (genChallenges curve pubKeys y msg g h sK2ToPrevSK)
      (initState sK1 u y)
    initState sK1 u y =
      (((k + 1) `mod` participants, sK1, chK1 u y), [chK1 u y])
    -- H(L, y, m, [u] * g, [u] * h)
    chK1 u y = genChallenge curve pubKeys y msg (gu u) (hu u)
    orderChallenges ch =
      drop (participants - k) ch <>
      take (participants - k) ch
    orderSS sKToPrevSK =
      drop (participants - (k - 1)) sKToPrevSK <>
      take (participants - (k - 1)) sKToPrevSK

verify
  :: [ECDSA.PublicKey]                    -- ^ List of participants public keys
  -> (Integer, [Integer], ECC.Point)      -- ^ Signature
  -> ByteString                           -- ^ Message
  -> IO Bool
verify pubKeys (ch1, s1:s2:s3ToSN, y) msg = do
  -- print "---------- Verified h -------------"
  -- print h
  print "----------------- ch1 ---------------"
  print ch1
  print "----------------- c1' ---------------"
  print ch1'
  -- print "----------------- Verified Challenges ---------------"
  -- print challenges
  print "----------------- Verified Ordered Challenges ---------------"
  print $ ch1' : reverse (tail challenges)

  pure $ ch1 == ch1'
  where
    -- TODO: Treat each public key with its curve
    -- We assume for now that all curves are the same
    curve = ECDSA.public_curve $ head pubKeys
    -- In ECC, h is a point in the curve. h = g x H_2(L)
    -- Compute y = h x x_pi
    h = ECC.pointBaseMul curve (hashPubKeys curve pubKeys)
    y1 = ECDSA.public_q $ head pubKeys
    -- z1' = [s1] * g + [c1] * y1
    z1' = ECC.pointAdd curve
      (ECC.pointMul curve s1 g)
      (ECC.pointMul curve ch1 y1)
    -- z1'' = [si] * h + [ci] * y
    z1'' = ECC.pointAdd curve
      (ECC.pointMul curve s1 h)
      (ECC.pointMul curve ch1 y)
    g = ECC.ecc_g (ECC.common_curve curve)
    participants = length pubKeys

    -- initial challenge - ch_2
    ch2 = genChallenge curve pubKeys y msg z1' z1''
    -- [ch1, chN ..., ch3, ch2]
    challenges = evalState
      (genChallenges curve pubKeys y msg g h s3ToSN)
      ((2 `mod` participants, s2, ch2), [ch2])
    ch1' = head challenges

genChallenges
  :: ECC.Curve
  -> [ECDSA.PublicKey]  -- ^ List of public keys L
  -> ECC.Point          -- ^ y = h x [x]
  -> BS.ByteString      -- ^ message msg
  -> ECC.Point          -- ^ generator g
  -> ECC.Point          -- ^ h = H(L)
  -> [Integer]          -- ^ random ss
  -> State ((Int, Integer, Integer), [Integer]) [Integer]
genChallenges c pubKeys y msg g h ss = do
  ((prevK, prevS, prevCh), challenges) <- get
  -- let ch = fromIntegral prevK
  let ch = challenge prevK prevS prevCh
  case ss of
    [] -> pure $ ch : challenges
    (s:ss) -> do
      put (((prevK + 1) `mod` participants, s, ch)
          , ch : challenges
          )
      genChallenges c pubKeys y msg g h ss
  where
    gs prevK prevS prevCh =
      ECC.pointAdd c
        (ECC.pointMul c prevS g)
        (ECC.pointMul c prevCh (ECDSA.public_q $ pubKeys !! prevK))
    hs prevK prevS prevCh =
      ECC.pointAdd c (ECC.pointMul c prevS h) (ECC.pointMul c prevCh y)
    challenge prevK prevS prevCh =
       genChallenge c pubKeys y msg (gs prevK prevS prevCh) (hs prevK prevS prevCh)
    participants = length pubKeys

-- | Generate challenge from a given message
--
-- @c = H(L, y, m, g^u, h^u)@
genChallenge
  :: ECC.Curve
  -> [ECDSA.PublicKey]  -- ^ List of public keys L
  -> ECC.Point          -- ^ y = h x [x]
  -> BS.ByteString      -- ^ message msg
  -> ECC.Point          -- ^ generator g
  -> ECC.Point          -- ^ h = H(L)
  -> Integer
-- TODO: Take curve from public keys
genChallenge c pubKeys y msg g h =
  oracle c (pubKeys' <> y' <> msg <> g' <> h')
  where
    pubKeys' = pubKeysToBS pubKeys
    y' = pointToBS y
    g' = pointToBS g
    h' = pointToBS h

insertPubKey :: Int -> ECDSA.PublicKey -> [ECDSA.PublicKey] -> [ECDSA.PublicKey]
insertPubKey k pubKey pubKeys = take k pubKeys <> [pubKey] <> drop k pubKeys

-- | Generate N different public keys. @L = {y1, ..., yn}@
genNPubKeys :: MonadRandom m => ECC.Curve -> Int -> m [ECDSA.PublicKey]
genNPubKeys curve n = replicateM n (fst <$> ECC.generate curve)

pointToBS :: ECC.Point -> BS.ByteString
pointToBS ECC.PointO      = ""
pointToBS (ECC.Point x y) = show x <> show y

pubKeysToBS :: [ECDSA.PublicKey] -> BS.ByteString
pubKeysToBS = foldMap (pointToBS . ECDSA.public_q)

hashPubKeys :: ECC.Curve -> [ECDSA.PublicKey] -> Integer
hashPubKeys c = oracle c . pubKeysToBS

oracle :: ECC.Curve -> BS.ByteString -> Integer
oracle curve x = os2ip (sha256 x) `mod` n
  where
    n = ECC.ecc_n (ECC.common_curve curve)

sha256 :: BS.ByteString -> BS.ByteString
sha256 bs = BA.convert (hash bs :: Digest SHA3_256)
