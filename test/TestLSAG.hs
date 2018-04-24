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
    [ Curve $ ECC.getCurveByName ECC.SEC_p192r1
    , Curve secp256k1Curve
    , Curve $ ECC.getCurveByName ECC.SEC_p256r1
    , Curve $ ECC.getCurveByName ECC.SEC_p384r1
    ]

-- | Insert element at specified position
insert :: Int -> a -> [a] -> [a]
insert k e l = take k l <> [e] <> drop k l

testLSAG :: TestTree
testLSAG = testGroup "LSAG Signature"
  [ localOption (QuickCheckTests 20) $ testProperty
      "Verify signature on SEC curves"
      (forAll (choose (3, 20)) testSignature)
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
  signature <- liftIO $ sign pubKeys (pubKey, privKey) k (show msg)
  -- Verify signature
  pure $ verify pubKeys signature (show msg)
