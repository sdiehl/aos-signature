module TestLSAG where

import           Protolude
import           Test.QuickCheck.Monadic
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck
import           Crypto.Number.Generate     (generateBetween)
import qualified Crypto.PubKey.ECC.Prim as ECC
import qualified Crypto.PubKey.ECC.Types as ECC
import qualified Crypto.PubKey.ECC.Generate as ECC

import           LSAG

testLSAG :: TestTree
testLSAG = testGroup "LSAG Signature"
  [ localOption (QuickCheckTests 10) $ testProperty
      "Verify signature"
      (forAll (choose (3, 50)) (testSignature secp256k1Curve))
  ]

testSignature
  :: ECC.Curve
  -> Int
  -> [Char]
  -> Property
testSignature curve nParticipants msg = monadicIO $ do
  -- Gen public and private keys
  (pubKey, privKey) <- liftIO $ ECC.generate curve
  -- Random foreign participants
  extPubKeys <- liftIO $ genNPubKeys curve nParticipants
  -- k: position of the signer's key in the public keys list
  k <- liftIO $ fromInteger <$> generateBetween 0 (toInteger $ length extPubKeys - 1)
  let pubKeys = insert k pubKey extPubKeys
  -- Sign message with list of public keys and signer's key pair
  signature <- liftIO $ sign pubKeys (pubKey, privKey) k (show msg)
  -- Verify signature
  pure $ verify pubKeys signature (show msg)
