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
  k <- fromInteger <$> generateBetween 1 (fromIntegral $ length extPubKeys - 1)
  let pubKeys = insertPubKey k pubKey extPubKeys
  signature <- sign curve pubKeys (pubKey, privKey) k msg
  print signature
  pure $ verify curve pubKeys signature msg

sign
  :: MonadRandom m
  => ECC.Curve                            -- ^ Curve
  -> [ECDSA.PublicKey]                    -- ^ List of public keys
  -> (ECDSA.PublicKey, ECDSA.PrivateKey)  -- ^ Signer's public and private keys
  -> Int                                  -- ^ Signer's position in list L
  -> ByteString                           -- ^ Message
  -> m (Integer, [Integer], ECC.Point)
sign curve pubKeys (pubKey, privKey) k msg = do
  let participants = length pubKeys

  --------------------- STEP 1 -----------------------
  -- In ECC, h is a point in the curve. h = g x H_2(L)
  -- Compute y = h x x_pi
  let h = ECC.pointBaseMul curve (hashPubKeys curve pubKeys)
      y = ECC.pointMul curve (ECDSA.private_d privKey) h

  --------------------- STEP 2 -----------------------
  -- Pick u and compute challenge c = H(L, y, m, g^u, h^u)
  u <- generateBetween 1 (n - 1)
  let msg = "hello world"
  -- Initial challenge on k + 1
  let initialChallenge = genChallenge curve pubKeys y msg (gu u) (hu u) u

  -- Generate L random s values
  ss <- replicateM (participants - 1) $ generateBetween 1 (n - 1)

  --------------------- STEP 3 -----------------------
  -- Generate challenges
  -- Challenges start at (k + 1)
  let initialState = (((k + 1) `mod` participants, u, initialChallenge), [initialChallenge])
  -- reversed [ck + 1, ck + 2, ... cn, 1, ... ck]
  let challenges = evalState (genChallenges curve pubKeys y msg g h ss) initialState
      revChallenges = reverse challenges
      ck = head challenges

  --------------------- STEP 4 -----------------------
  -- Compute s = u - x * c mod q
  let s = u - ECDSA.private_d privKey * ck `mod` n

  -- [c1, c2, ..., cn]
  let ordChallenges = drop (participants - k) revChallenges <> take (participants - k) revChallenges

  -- [s1, s2, ..., sk, ..., sn]
  let ordSS = drop (participants - k) ss <> [s] <> take (participants - k) ss

  -- The signature is (c1, s1, ..., sn, y)
  let c1 = head ordChallenges

  pure (c1, ordSS, y)
  where
    n = ECC.ecc_n (ECC.common_curve curve)
    g = ECC.ecc_g (ECC.common_curve curve)
    gu u = pointToBS (ECC.pointMul curve u g)
    hu u = pointToBS (ECC.pointMul curve u g)

verify
  :: ECC.Curve                            -- ^ Curve
  -> [ECDSA.PublicKey]                    -- ^ List of participants public keys
  -> (Integer, [Integer], ECC.Point)      -- ^ Signature
  -> ByteString                           -- ^ Message
  -> Bool
verify c pubKeys signature@(c1, ss, y) msg = c1 == c1'

  where
    gs k s ch =
      pointToBS $
        ECC.pointAdd c
          (ECC.pointMul c s g)
          (ECC.pointMul c ch (ECDSA.public_q $ pubKeys !! k))
    hs h k s ch =
      pointToBS $ ECC.pointAdd c (ECC.pointMul c s h) (ECC.pointMul c ch y)
    g = ECC.ecc_g (ECC.common_curve c)
    participants = length pubKeys
    --------------------- STEP 1 -----------------------
    -- In ECC, h is a point in the curve. h = g x H_2(L)
    -- Compute y = h x x_pi
    h = ECC.pointBaseMul c (hashPubKeys c pubKeys)
    s = head ss
    z1 = gs 0 s c1
    z1' = hs h 0 s c1

    -- initial challenge -> ch_2
    initialChallenge = genChallenge c pubKeys y msg z1 z1' s
    initialState = ((1 `mod` participants, s, initialChallenge), [initialChallenge])
    challenges = evalState (genChallenges c pubKeys y msg g h ss) initialState
    c1' = head challenges


-- | Generate challenge from a given message
--
-- @c = H(L, y, m, g^u, h^u)@
genChallenge
  :: ECC.Curve
  -> [ECDSA.PublicKey]  -- ^ List of public keys L
  -> ECC.Point          -- ^ y = h x [x]
  -> BS.ByteString      -- ^ message msg
  -> BS.ByteString      -- ^ generator g
  -> BS.ByteString      -- ^ h = H(L)
  -> Integer            -- ^ random u
  -> Integer
genChallenge c vks y msg g h u =
  oracle c (vks' <> y' <> msg <> g <> h)
  where
    vks' = pubKeysToBS vks
    y' = pointToBS y

genChallenges
  :: ECC.Curve
  -> [ECDSA.PublicKey]  -- ^ List of public keys L
  -> ECC.Point          -- ^ y = h x [x]
  -> BS.ByteString      -- ^ message msg
  -> ECC.Point          -- ^ generator g
  -> ECC.Point          -- ^ h = H(L)
  -> [Integer]          -- ^ random ss
  -> State ((Int, Integer, Integer), [Integer]) [Integer]
genChallenges c vks y msg g h [] = do
  (_, challenges) <- get
  pure challenges

genChallenges c vks y msg g h (s:ss) = do
  ((prevPos, prevS, prevChallenge), challenges) <- get
  let challenge = nextChallenge prevPos prevS prevChallenge
  modify $ \st ->
      (((prevPos + 1) `mod` length vks, s, challenge)
      , challenge : snd st
      )
  genChallenges c vks y msg g h ss

  where
    gs prevPos prevS prevChallenge =
      pointToBS $
        ECC.pointAdd c
          (ECC.pointMul c prevS g)
          (ECC.pointMul c prevChallenge (ECDSA.public_q $ vks !! prevPos))
    hs prevPos prevS prevChallenge =
      pointToBS $ ECC.pointAdd c (ECC.pointMul c prevS h) (ECC.pointMul c prevChallenge y)
    nextChallenge prevPos prevS prevChallenge = genChallenge c vks y msg (gs prevPos prevS prevChallenge) (hs prevPos prevS prevChallenge) s


insertPubKey :: Int -> ECDSA.PublicKey -> [ECDSA.PublicKey] -> [ECDSA.PublicKey]
insertPubKey k vk vks = take k vks <> [vk] <> drop k vks

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
