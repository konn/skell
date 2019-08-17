{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, RecordWildCards #-}
module Data.HEnv where
import           Data.Hashable
import           Data.HashMap.Strict   (HashMap)
import qualified Data.HashMap.Strict   as HM
import           Language.Skell.Syntax
import           Numeric.Natural

newtype HEnv v = HEnv { natDic :: HashMap v Natural }

instance (Eq v, Hashable v) => Semigroup (HEnv v) where
  HEnv l <> HEnv r = HEnv $ HM.union l r

instance (Eq v, Hashable v) => Monoid (HEnv v) where
  mempty = HEnv HM.empty

class HEnvLookup v a where
  lookup :: v -> HEnv v -> Maybe (View v a)

instance {-# OVERLAPPABLE #-} HEnvLookup v a where
  lookup = const $ const Nothing

instance {-# OVERLAPPING #-}
  (Hashable v, Eq v) => HEnvLookup v Natural where
  lookup v HEnv{..} = I <$> HM.lookup v natDic
