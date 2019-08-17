{-# LANGUAGE AllowAmbiguousTypes, BangPatterns, ConstraintKinds, DataKinds #-}
{-# LANGUAGE DefaultSignatures, DeriveAnyClass, DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric                  #-}
{-# LANGUAGE DeriveTraversable, DerivingStrategies, FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances, GADTs, GeneralizedNewtypeDeriving          #-}
{-# LANGUAGE LambdaCase, MultiParamTypeClasses, PolyKinds, RankNTypes      #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeApplications     #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances             #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Data.Unification.Generic
  ( Equation(..), (%==), Subst(..), UTree, UnificationError(..)
  , WithMetaVarCon(..), matchWithMetaVarCon
  , hoistEq, decompEq, matchFree
  , metavars
  , Unify, UnifyT(..), HasCons1, Cons1Path
  , unifyM, unify
  , Cons1PathM
  , GetParPath
  , Matchable(..), GMatchable
  , substituteFree
  , substitute, substituteM
  ) where
import           Control.Applicative
import           Control.Arrow
import           Control.Exception                (Exception)
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Free
import           Control.Monad.Trans.State.Strict
import           Data.Coerce
import           Data.Foldable
import           Data.Function
import           Data.Functor.Classes
import           Data.Functor.Identity
import           Data.Hashable
import           Data.Hashable.Lifted
import           Data.HashMap.Strict              (HashMap)
import qualified Data.HashMap.Strict              as HM
import           Data.HashSet                     (HashSet)
import qualified Data.HashSet                     as HS
import           Data.Maybe
import           Data.Monoid
import           Data.Proxy
import           Data.Typeable
import           Data.TypeLevel.Path.Parametric
import           GHC.Generics
import           GHC.TypeLits
import           Unsafe.Coerce

newtype UnifyT t v m a =
  UnifyT { runUnifyT :: StateT (Subst t v) (ExceptT (First (UnificationError t v)) m)  a }
  deriving newtype (Functor, Applicative, Monad, MonadPlus, Alternative)

data UnificationError t v =
    OccurrenceError v (UTree t v)
  | Mismatch (UTree t v) (UTree t v)
    deriving (Read, Show, Eq, Ord, Generic, Exception, Typeable)

type Unify t v  = UnifyT t v Identity

instance Monad m => MonadError (UnificationError t v) (UnifyT t v m) where
  throwError = UnifyT . lift . throwError . First . Just
  catchError (UnifyT a) f = UnifyT $ liftCatch catchError a $
    runUnifyT . f . fromJust . getFirst

metavars :: (Foldable t, Eq v, Hashable v) => t v -> HashSet v
metavars = HS.fromList . toList

type UTree t v = Free t v
newtype Subst t v = Subst { runSubst :: HashMap v (UTree t v) }
    deriving (Read, Show, Eq, Ord, Generic)
    deriving newtype (Semigroup, Monoid)

data UnifyStep t v =
    NewSubst   (Subst t v)
  | NewClauses (HashSet (Equation t v))
  deriving (Read, Show, Eq, Ord, Generic)

newSubst :: (Functor t, Eq v, Hashable v, Monad m)
         => v -> Free t v -> UnifyT t v m (UnifyStep t v)
newSubst v t = UnifyT $ do
  substs <- get
  let subs = Subst $ HM.singleton v (substituteFree substs t)
  put $ coerce (HM.map (substituteFree subs)) substs <> subs
  return $ NewSubst subs

step
  :: (Foldable t, Matchable t, Monad m, Hashable v, Eq v)
  => Equation t v -> UnifyT t v m (UnifyStep t v)
step (Pure l :== Pure r) = newSubst l (Pure r)
step (e :== Pure v) = step (Pure v :== e)
step (Pure v :== e)
  | v `elem` e = throwError $ OccurrenceError v e
  | otherwise = newSubst v e
step (l :== r) =
  case matchFree l r of
    Nothing  -> throwError $ Mismatch l r
    Just eqs -> return $ NewClauses $ HS.fromList eqs

unifyM
  :: ( Monad m, Matchable t, Eq v,
       Hashable v, Foldable t, Eq1 t, Hashable1 t
     )
  => [Equation t v]
  -> m (Either (UnificationError t v) (Subst t v))
unifyM =
    fmap (left $ fromJust . getFirst)
  . runExceptT
  . flip execStateT mempty
  . runUnifyT . go . HS.fromList
  where
  go !inp
    | null inp = return ()
    | otherwise = getAlt (foldMap (\ a -> Alt $ (,) a <$> step a) inp) >>= \case
        (a, NewSubst subs) -> go $ HS.map (substEq subs) $ HS.delete a inp
        (a, NewClauses eqs) -> go $ eqs <> HS.delete a inp

unify
  :: (Matchable t, Eq v, Hashable v, Foldable t,
      Eq1 t, Hashable1 t
    )
  => [Equation t v]
  -> Either (UnificationError t v) (Subst t v)
unify = runIdentity . unifyM

matchFree :: (Matchable t, Eq a) => UTree t a -> UTree t a -> Maybe [Equation t a]
matchFree l r = map (mapEq retract) <$> match l r

data Equation t a = Free t a :== Free t a
  deriving (Read, Show, Eq, Ord, Generic, Generic1,
            Functor, Foldable, Traversable)
  deriving anyclass (Hashable1)
infix 4 :==

(%==) :: Functor t => t a -> t a -> Equation t a
(%==) = (:==) `on` liftF
infix 4 %==

hoistEq :: Functor u => (forall x. t x -> u x) -> Equation t a -> Equation u a
{-# INLINE [1] hoistEq #-}
hoistEq t (l :== r) = hoistFree t l :== hoistFree t r

deriving anyclass instance (Hashable1 t, Functor t) => Hashable1 (Free t)
instance (Functor t, Hashable1 t, Hashable v)
      => Hashable (Equation t v) where
  hashWithSalt = hashWithSalt1

class (Functor t, Eq1 t, Hashable1 t) => Matchable t where
  match :: Eq v => t v -> t v -> Maybe [Equation t v]

  default match
    :: (GMatchable t, Eq v)
    => t v -> t v -> Maybe [Equation t v]
  match = defaultMatch

defaultMatch
  :: (GMatchable t)
  => t v -> t v -> Maybe [Equation t v]
defaultMatch = gmatch `on` from1

deriving anyclass instance Matchable Maybe
deriving anyclass instance Matchable []

type GMatchable t =
    ( Functor t, Eq1 t, Hashable1 t, Generic1 t,
      GMatchable' t (Rep1 t) (Rep1 t)
    )

newtype WithMetaVarCon t (c :: Symbol) v
  = WithMetaVarCon { runWithMetaVarCon :: t v }
  deriving newtype (Functor, Foldable, Applicative, Monad, Hashable1, Eq1)

proj :: forall s f a. (Generic1 f, HasCons1 s f) => f a -> Maybe a
proj = walkParPath (parPath @(Rep1 f) @(Cons1Path s f) Proxy)

instance (GMatchable t, HasCons1 s t)
      => Matchable (WithMetaVarCon t s) where
  match =
    fmap (fmap unsafeCoerce)
    (matchWithMetaVarCon @s @t `on` runWithMetaVarCon)

matchWithMetaVarCon
  :: forall s t v. (Eq v, GMatchable t, HasCons1 s t)
  => t v -> t v -> Maybe [Equation t v]
matchWithMetaVarCon l r =
  case (proj @s l, proj @s r) of
    (Just v, Just u)
      | v == u -> Just []
      | otherwise ->  Just $ pure $ Pure v :== Pure u
    (Nothing, Just v) -> Just $ pure $ Pure v :== liftF l
    (Just v, Nothing) -> Just $ pure $ Pure v :== liftF r
    _                 -> defaultMatch l r

substitute
  :: (Eq v, Hashable v, Functor t)
  => Subst t v
  -> t v
  -> UTree t v
substitute dic = substituteFree dic . liftF

substituteFree
  :: (Eq v, Hashable v, Functor t)
  => Subst t v
  -> UTree t v
  -> UTree t v
substituteFree (Subst subst) = (>>= look)
  where look v = fromMaybe (return v) $ HM.lookup v subst

substituteM
  :: (Eq v, Hashable v, Monad t)
  => Subst t v -> t v -> t v
substituteM dic = retract . substitute dic

substEq
  :: (Eq v, Hashable v, Foldable t, Functor t)
  => Subst t v -> Equation t v -> Equation t v
substEq s = mapEq (substituteFree s)

eqFree
  :: Functor t
  => Equation t (Free t v)
  -> Equation (Free t) v
eqFree = mapEq (liftF . join)

unEqFree
  :: Functor t
  => Equation (Free t) v
  -> Equation t v
unEqFree = mapEq retract

mapEq :: (Free t1 a1 -> Free t2 a2) -> Equation t1 a1 -> Equation t2 a2
mapEq f (l :== r) = f l :== f r

instance (Matchable t) => Matchable (Free t) where
  match (Pure v) (Pure u) = Just [Pure v :== Pure u]
  match (Free v) (Pure u) = match (Pure u) (Free v)
  match (Pure u) (Free e) = Just [Pure u :== liftF (Free e)]
  match (Free v) (Free u) = map eqFree <$> match v u

decompEq :: (Eq v, Matchable t) => Equation t v -> Maybe [Equation t v]
decompEq (l :== r) = map unEqFree <$> match l r

class GMatchable' t p q where
  gmatch :: p v -> q v -> Maybe [Equation t v]

instance {-# OVERLAPPABLE #-} GMatchable' a f g where
  gmatch = const $ const Nothing

instance GMatchable' t f g => GMatchable' t (M1 i c f) (M1 i c g) where
  gmatch (M1 a) (M1 b) = gmatch a b

instance (GMatchable' t f f', GMatchable' t g g')
      => GMatchable' t (f :+: g) (f' :+: g') where
  gmatch (L1 a) (L1 a') = gmatch a a'
  gmatch (R1 b) (R1 b') = gmatch b b'
  gmatch _ _            = Nothing

instance (Functor t, Hashable1 t, Eq1 t, GMatchable' t f f', GMatchable' t g g')
      => GMatchable' t (f :*: g) (f' :*: g') where
  gmatch (a :*: b) (a' :*: b') =
    (<>) <$> gmatch a a' <*> gmatch b b'

instance (Functor t, Hashable1 t, Eq1 t)
      => GMatchable' t Par1 Par1 where
  gmatch (Par1 v) (Par1 u) = Just [Pure v :== Pure u]

instance (Functor t, Hashable1 t, Eq1 t) => GMatchable' t Par1 (Rec1 t) where
  gmatch (Par1 v) (Rec1 f) = Just [Pure v :== liftF f]

instance (Functor t, Hashable1 t, Eq1 t) => GMatchable' t (Rec1 t) Par1 where
  gmatch (Rec1 f) (Par1 v) = Just [Pure v :== liftF f]

instance (Functor t, Hashable1 t, Eq1 t) => GMatchable' t (Rec1 t) (Rec1 t) where
  gmatch (Rec1 f) (Rec1 g) = Just [liftF f :== liftF g]

instance GMatchable' t U1 U1 where
  gmatch U1 U1 = Just []

instance GMatchable' t V1 V1 where
  gmatch = const $ const $ Just []

instance Eq v => GMatchable' t (K1 i v) (K1 i v) where
  gmatch (K1 a) (K1 b) = guard (a == b) >> pure []
