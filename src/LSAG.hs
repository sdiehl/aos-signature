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

testSignature :: MonadRandom m => ECC.Curve -> m (Integer, [Integer], ECC.Point)
testSignature curve = do
  (vk, sk) <- ECC.generate curve

  -- SETUP
  -- Create list of public keys
  let participants = 10
  vks' <- genNPubKeys curve participants
  -- k -> position of the signer's key in the list of public keys
  k <- fromInteger <$> generateBetween 1 (fromIntegral participants - 1)
  let vks = insertPubKey k vk vks'

  -- STEP 1
  -- In ECC, h is a point in the curve. h = g x H_2(L)
  -- Compute y = h x x_pi
  let h = ECC.pointBaseMul curve (hashPubKeys curve vks)
      y = ECC.pointMul curve (ECDSA.private_d sk) h

  -- STEP 2
  -- Pick u and compute challenge c = H(L, y, m, g^u, h^u)
  u <- generateBetween 1 (n - 1)
  let msg = "hello world"
  -- Initial challenge on k + 1
  let initialChallenge = genChallenge curve vks y msg (gu u) (hu u) u

  -- Generate L random s values
  ss <- replicateM participants $ generateBetween 1 (n - 1)

  -- Generate challenges
  -- Challenges start at (k + 1)
  let initialState = (((k + 1) `mod` length vks, u, initialChallenge), [initialChallenge])
  -- reversed [ck + 1, ck + 2, ... cn, 1, ... ck]
  let challenges = evalState (genChallenges curve vks y msg g h u ss) initialState
  let ck = head challenges
  -- Compute s = u - x * c mod q
  let s = u - ECDSA.private_d sk * ck `mod` n
  -- [c1, c2, ..., cn]
  let ordChallenges = drop (length vks - k) (reverse challenges) <> take (length vks - k) (reverse challenges)
  -- [s1, s2, ..., sk, ..., sn]
  let ordSS = drop (length vks - k) ss <> [s] <> take (length vks - k) ss

  -- The signature is (c1, s1, ..., sn, y)
  let c1 = head ordChallenges
  pure (c1, ordSS, y)
  where
    n = ECC.ecc_n (ECC.common_curve curve)
    g = ECC.ecc_g (ECC.common_curve curve)
    gu u = pointToBS (ECC.pointMul curve u g)
    hu u = pointToBS (ECC.pointMul curve u g)

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
  -> Integer            -- ^ u
  -> [Integer]          -- ^ random ss
  -> State ((Int, Integer, Integer), [Integer]) [Integer]
genChallenges c vks y msg g h u [] = do
  (_, challenges) <- get
  pure challenges

genChallenges c vks y msg g h u (s:ss) = do
  ((prevPos, prevS, prevChallenge), challenges) <- get
  let challenge = nextChallenge prevPos prevS prevChallenge
  modify $ \st ->
      (((prevPos + 1) `mod` length vks, s, challenge)
      , challenge : snd st
      )
  genChallenges c vks y msg g h u ss

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
