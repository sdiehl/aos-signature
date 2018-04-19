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

testSignature :: MonadRandom m => m [Integer]
testSignature = do
  (vk, sk) <- ECC.generate secp256k1Curve

  -- Create list of public keys
  let vksLen' = 10
  vks' <- genNPubKeys secp256k1Curve vksLen'
  pos <- fromInteger <$> generateBetween 1 (fromIntegral vksLen' - 1)
  let vks = insertPubKey pos vk vks'

  -- Compute h = H_2(L) and y = h^x_pi
  let h = ECC.pointBaseMul secp256k1Curve (hashPubKeys secp256k1Curve vks)
      y = ECC.pointMul secp256k1Curve (ECDSA.private_d sk) h

  -- Pick u and compute challenge c = H(L, y, m, g^u, h^u)
  u <- generateBetween 1 (n - 1)
  let msg = "hello world"
      c = secp256k1Curve
      challenge = genChallenge c vks y msg (gu u) (hu u) u

  -- Generate L random s values
  ss <- replicateM vksLen' $ generateBetween 1 (n - 1)

  -- generate challenge
  let initialState = ((pos + 1 `mod` length vks, u, challenge), [challenge])
      -- challenges start at (pi + 1)
      challenges = evalState (genChallenges c vks y msg g h u ss) initialState

  -- Compute s = u - x * c mod q
  let s = u - ECDSA.private_d sk * head challenges `mod` n

  -- The signature is (c1, s1, ..., sn, y)
  -- TODO: Reorder challenges
  -- TODO: Reorder ss
  -- TODO: get c1
  -- TODO: Return signature
  pure challenges
  where
    n = ECC.ecc_n (ECC.common_curve secp256k1Curve)
    g = ECC.ecc_g (ECC.common_curve secp256k1Curve)
    gu u = pointToBS (ECC.pointMul secp256k1Curve u g)
    hu u = pointToBS (ECC.pointMul secp256k1Curve u g)

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
  let ch = challenge prevPos prevS prevChallenge
  modify $ \st ->
      ((prevPos + 1 `mod` length vks, s, ch)
      , ch : snd st
      )
  genChallenges c vks y msg g h u ss

  where
    gs prevPos prevS prevChallenge =
      pointToBS $
        ECC.pointAdd c
          (ECC.pointMul c prevS g)
          (ECC.pointMul c prevChallenge (ECDSA.public_q $ vks !! (fromIntegral prevPos - 1)))
    hs prevPos prevS prevChallenge =
      pointToBS $ ECC.pointAdd c (ECC.pointMul c prevS h) (ECC.pointMul c prevChallenge y)
    challenge prevPos prevS prevChallenge = genChallenge c vks y msg (gs prevPos prevS prevChallenge) (hs prevPos prevS prevChallenge) s


insertPubKey :: Int -> ECDSA.PublicKey -> [ECDSA.PublicKey] -> [ECDSA.PublicKey]
insertPubKey pos vk vks = take pos vks <> [vk] <> drop pos vks

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
