{-# LANGUAGE DeriveAnyClass, DeriveGeneric, DerivingStrategies #-}
module Data.Fresh (Fresh(..), Var(..)) where
import Control.Monad
import Data.Foldable
import Data.Hashable
import Data.Semigroup
import Data.String
import GHC.Generics

class Fresh a where
  origin :: a
  fresh :: Foldable t => a -> t a -> a

data Var = VarE { baseName :: String, suffix :: Maybe Word }
  deriving (Eq, Ord, Generic)
  deriving anyclass (Hashable)

instance Show Var where
  showsPrec _ (VarE a Nothing)  = showString a
  showsPrec _ (VarE a (Just i)) = showString a . shows i

instance IsString Var where
  fromString = flip VarE Nothing

instance Fresh Int where
  origin = 0
  fresh _ = succ . maximum . (0:) . toList

instance Fresh Var where
  origin = VarE "#arg" Nothing
  fresh (VarE a _) =
    VarE a . fmap (maybe 0 (getMax . succ)) . foldMap loop
    where
      loop :: Var -> Maybe (Maybe (Max Word))
      loop (VarE b n) = do
        guard $ b == a
        return $ Max <$> n
