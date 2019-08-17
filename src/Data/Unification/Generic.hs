{-# LANGUAGE ConstraintKinds, DataKinds, DeriveAnyClass, DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor, DeriveGeneric, DeriveTraversable            #-}
{-# LANGUAGE DerivingStrategies, FlexibleContexts, FlexibleInstances    #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses          #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeApplications  #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances          #-}
module Data.Unification.Generic where
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Free
import           Control.Monad.State.Strict
import           Data.Coerce
import           Data.Foldable
import           Data.Fresh
import           Data.Hashable
import           Data.HashMap.Strict        (HashMap)
import qualified Data.HashMap.Strict        as HM
import           Data.HashSet               (HashSet)
import qualified Data.HashSet               as HS
import           Data.Kind
import           Data.Maybe
import           GHC.Generics
import           GHC.TypeLits

newtype Unify v a = Unify { runUnifyT :: StateT (HashSet v) Maybe a }
  deriving newtype (Functor, Applicative, Monad, Alternative, MonadPlus)

deriving newtype instance MonadState (HashSet v) (Unify v)

type UTree t v = Free t v
newtype Subst t v = Subst { runSubst :: HashMap v (UTree t v) }

data Equation t a = a :== t a
  deriving (Read, Show, Eq, Ord, Generic,
            Functor, Foldable, Traversable)
  deriving anyclass (Hashable)

class Functor t => Matchable t where
  match :: t v -> t v -> Maybe [Equation t v]

newtype WithVarCon t (c :: Symbol) v
  = WithVarCon { runWithVarCon :: t v }
  deriving newtype (Functor, Foldable)

getParameter :: (Generic1 t, GGetParameter (Rep1 t)) => t v -> Maybe v
getParameter = gGetParameter . from1

class GGetParameter f where
  gGetParameter :: f a -> Maybe a

instance GGetParameter f => GGetParameter (M1 i c f) where
  gGetParameter = gGetParameter @f . unM1

instance (GGetParameter f, GGetParameter g)
      => GGetParameter (f :+: g) where
  gGetParameter (L1 f) = gGetParameter f
  gGetParameter (R1 f) = gGetParameter f

instance GGetParameter Par1 where
  gGetParameter (Par1 a) = Just a

instance {-# OVERLAPPABLE #-}  GGetParameter f where
  gGetParameter = const Nothing

type family FromBool (msg :: ErrorMessage) (b :: Bool) :: Constraint where
  FromBool _ 'True  = ()
  FromBool m 'False = TypeError m

type family (||) (a :: Bool) (b :: Bool) :: Bool where
  'True  || _ = 'True
  'False || a = a

type HasCons1 s t =
  FromBool
    ('Text "A type `" ':<>: 'ShowType t
      ':<>: 'Text "' doesn't have a constructor "
      ':<>: 'ShowType s ':<>: 'Text " with the unique parametric argument.")
    (GHasCons1 s (Rep1 t))

type family GHasCons1 (s :: Symbol) t :: Bool where
  GHasCons1 s (D1 _ f) = GHasCons1 s f
  GHasCons1 s (l :+: r) = GHasCons1 s l || GHasCons1 s r
  GHasCons1 s (C1 ('MetaCons s _ _) f) = IsPar1 f
  GHasCons1 _ _ = 'False

type family IsPar1 t :: Bool where
  IsPar1 (C1 _ f)    = IsPar1 f
  IsPar1 (S1 _ Par1) = 'True
  IsPar1 _           = 'False


class GMatchable t p where
  gmatch :: (Hashable v, Eq v) => p v -> p v -> Maybe [Equation t v]

{-
instance GMatchable t f => GMatchable t (M1 i c f) where
  gmatch = coerce $ gmatch @f

instance GMatchable t V1 where
  gmatch = \case {}

instance GMatchable t U1 where
  gmatch = const $ const $ Just [] -}

-- instance (GMatchable f, GMatchable g) => GMatchable (f :*: g) where
--   gmatch (l :*: r) (l' :*: r') =
--     gmatch l l' <> gmatch r r'


freshMeta :: (Eq v, Hashable v, Fresh v) => Unify v v
freshMeta = do
  v <- fresh origin <$> get
  modify $ HS.insert v
  return v

markUsed :: (Foldable t, Hashable v, Eq v) => t v -> Unify v ()
markUsed = modify . HS.union . HS.fromList . toList

substitute
  :: (Eq v, Hashable v, Functor t)
  => Subst t v
  -> t v
  -> UTree t v
substitute (Subst subst) = (>>= look) . liftF
  where look v = fromMaybe (return v) $ HM.lookup v subst

substituteM
  :: (Eq v, Hashable v, Monad t)
  => Subst t v -> t v -> t v
substituteM dic = retract . substitute dic
