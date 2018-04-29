module TestLSAG where

import           Protolude
import           Test.QuickCheck.Monadic
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck
import           Crypto.Number.Generate     (generateBetween)
import qualified Crypto.PubKey.ECC.Prim     as ECC
import qualified Crypto.PubKey.ECC.Types    as ECC
import qualified Crypto.PubKey.ECC.Generate as ECC

import           LSAG

newtype Curve = Curve ECC.Curve deriving Show

secp256k1Curve :: ECC.Curve
secp256k1Curve = ECC.getCurveByName ECC.SEC_p256k1

instance Arbitrary Curve where
  arbitrary = elements
    [ Curve secp256k1Curve
    ]

genPoint :: ECC.Curve -> Gen ECC.Point
genPoint curve = ECC.generateQ curve <$> arbitrary

genPos :: Gen Integer
genPos = abs <$> arbitrary `suchThat` (> 0)

-- | Insert element at specified position
insert :: Int -> a -> [a] -> [a]
insert k e l = take k l <> [e] <> drop k l

testLSAG :: TestTree
testLSAG = testGroup "LSAG Signature"
  [ localOption (QuickCheckTests 10) $ testProperty
      "Verify signature on SEC curves"
      (forAll (choose (3, 20)) testSignature)
  , localOption (QuickCheckTests 50) $ testProperty
      "A verifier rejects invalid signatures"
      (forAll (choose (3, 15)) $ \nParticipants ->
      forAll genPos $ \challenge ->
      forAll (genPoint secp256k1Curve) $ \y ->
      testInvalidPubKeys nParticipants y challenge)
  ]

testSignature
  :: Int
  -> Curve
  -> Curve
  -> Curve
  -> Curve
  -> [Char]
  -> Property
testSignature
  nParticipants
  (Curve curve0)
  (Curve curve1)
  (Curve curve2)
  (Curve curve3)
  msg = monadicIO $ do
  -- Gen public and private keys
  (pubKey, privKey) <- liftIO $ ECC.generate curve0
  -- Gen random foreign participants
  extPubKeys1 <- liftIO $ genNPubKeys curve1 nParticipants
  extPubKeys2 <- liftIO $ genNPubKeys curve2 nParticipants
  extPubKeys3 <- liftIO $ genNPubKeys curve3 nParticipants
  let extPubKeys = extPubKeys1 <> extPubKeys2 <> extPubKeys3
  -- k: position of the signer's key in the public keys list
  k <- liftIO $ fromInteger <$> generateBetween 0 (toInteger $ length extPubKeys - 1)
  let pubKeys = insert k pubKey extPubKeys
  -- Sign message with list of public keys and signer's key pair
  signature <- liftIO $ sign pubKeys (pubKey, privKey) (show msg)
  -- Verify signature
  pure $ verify pubKeys signature (show msg)


-- | A verifier rejects an invalid signature
testInvalidPubKeys
  :: Int
  -> ECC.Point
  -> Integer
  -> Curve
  -> [Char]
  -> Property
testInvalidPubKeys nParticipants y ch0 (Curve curve) msg = monadicIO $ do
  ss <- liftIO $ replicateM nParticipants $ generateBetween 1 n
  pubKeys <- liftIO $ genNPubKeys curve nParticipants
  pure $ not $ verify pubKeys (ch0, ss, y) (show msg)
  where
    n = ECC.ecc_n (ECC.common_curve curve)
