module Language.Skell.EvalSpec where
import Language.Skell.Eval
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

spec :: Spec
spec = do
  describe "withSig" $ do
    prop "is left-inverse to `decodeSig'" $ property $ \(NonNegative a) ->
      a === toInteger (withSig (decodeSig $ fromInteger a))
    prop "is right-inverse to `decodeSig'" $ property $ \a ->
      a === decodeSig (withSig a)
  describe "prWord" $ do
    prop "is left-inverse to `unpairWord'" $ \(NonNegative a) ->
      a === toInteger (uncurry prWord (unpairWord $ fromInteger a))
    prop "is right-inverse to `unpairWord'" $ \(NonNegative a) (NonNegative b) ->
      (fromInteger a, fromInteger b) === unpairWord (prWord (fromInteger a) (fromInteger b))
  describe "pair" $
    prop "is right-inverse to `unpair'" $ \a b ->
      (a, b) === unpair (pair a b)
  describe "decodeString" $
    prop "is left-inverse to `encodeString'" $ \a ->
      a === decodeString (encodeString a)

