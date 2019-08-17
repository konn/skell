{-# LANGUAGE DataKinds, DeriveAnyClass, DeriveFoldable, DeriveFunctor  #-}
{-# LANGUAGE DeriveGeneric, DeriveTraversable, DerivingVia             #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, LiberalTypeSynonyms  #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings, PatternSynonyms #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TemplateHaskell          #-}
{-# LANGUAGE TypeApplications, TypeOperators, UndecidableInstances     #-}
{-# LANGUAGE ViewPatterns                                              #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Language.Skell.Syntax.Untyped where
import           Control.Arrow               hiding (arr, loop)
import           Control.Exception           (Exception)
import           Control.Monad
import           Control.Monad.Except
import qualified Control.Monad.Reader.Class  as R
import           Control.Monad.Trans.RWS.CPS
import qualified Control.Monad.Writer.Class  as W
import qualified Data.Bifunctor              as B
import           Data.Bifunctor.TH
import           Data.Deriving
import qualified Data.Fresh                  as F
import           Data.Fresh.Monad
import           Data.Functor.Classes
import           Data.Hashable
import           Data.Hashable.Lifted
import           Data.HashMap.Strict         (HashMap)
import qualified Data.HashMap.Strict         as HM
import           Data.HashSet                (HashSet)
import qualified Data.HashSet                as HS
import           Data.Monoid
import           Data.Typeable
import           Data.Unification.Generic
import           Data.Void
import           GHC.Generics
import           Language.Skell.Syntax       hiding (abstract)
import           Numeric.Natural

data UExpr' u v s
  = UPrimI s Natural
  | UVar s v
  | UPrimOp s PrimOp (UExpr' u v s)
  | UPrimBin s PrimBin (UExpr' u v s) (UExpr' u v s)
  | UIfte s (UExpr' u v s) (UExpr' u v s) (UExpr' u v s)
  | ULam s (u -> UExpr' u v s)
  | UFix s (UExpr' u v s)
  | UApp s (UExpr' u v s) (UExpr' u v s)
    deriving (Generic, Functor)

class HasAnn a where
  addAnn :: Int -> a -> ShowS -> ShowS
  toApp :: a -> ShowS

instance HasAnn () where
  addAnn = const $ const id
  toApp = const id

instance {-# OVERLAPPABLE #-} Show a => HasAnn a where
  addAnn d a v = showParen (d > 10) $ v . showString " : " . shows a
  toApp a = showString " @" . showsPrec 11 a

instance (HasAnn s, Show v, Hashable v, Eq v, F.Fresh v) => Show (UExpr' v v s) where
  showsPrec = (runFresh .) . go
    where
      go _ (UVar s v)   = do
        reserve v
        return $ addAnn 11 s (shows v)
      go _ (UPrimI s n) = return $ addAnn 11 s (shows n)
      go _ (UPrimOp s op e) = do
        n <- go 11 e
        return $
          showParen True $
          addAnn 10 s (prettyOp op . showChar ' ' . n)
      go _ (UPrimBin s op l r) = do
        n <- go 11 l
        m <- go 11 r
        return $
          showParen True $
          addAnn 10 s (prettyBin op . showChar ' ' . n . showChar ' ' . m)
      go _ (UIfte s p t e) = do
        sp <- go 11 p
        st <- go 11 t
        se <- go 11 e
        return $ showParen True $
          showString "if" .
          toApp s . showChar ' '
          . sp . showChar ' '
          . st . showChar ' '
          . se
      go _ (UFix s f) = do
        bdy <- go 11 f
        return $ showParen True $
          showString "fix" . toApp s
          . showChar ' ' . bdy
      go d (UApp s l r) = do
        f <- go 10 l
        a <- go 11 r
        return $ addAnn d s $
          f . showChar ' ' . a
      go _ (ULam s b) = do
        v <- fresh Nothing
        bdy <- go 11 $ b v
        return $ showParen True $
          showString "lam" . toApp s
          . showString " [" . shows v . showChar ']'
          . showChar ' ' . bdy

deriveBifunctor ''UExpr'

mapFV :: (v -> v') -> UExpr' u v s -> UExpr' u v' s
mapFV = B.first

cmapBV :: (u' -> u) -> UExpr' u v s -> UExpr' u' v s
cmapBV f = loop
  where
    loop (UPrimI s n)        = UPrimI s n
    loop (UVar s v)          = UVar s v
    loop (UApp s l r)        = UApp s (loop l) (loop r)
    loop (ULam s b)          = ULam s (loop . b . f)
    loop (UFix s a)          = UFix s (loop a)
    loop (UPrimOp s op e)    = UPrimOp s op (loop e)
    loop (UPrimBin s op l r) = UPrimBin s op (loop l) (loop r)
    loop (UIfte s p t e)     = UIfte s (loop p) (loop t) (loop e)
{-# INLINE cmapBV #-}

data BF b = B { fromB :: b } | F { fromF :: b }
  deriving (Read, Show, Eq, Ord, Functor)

markBF :: UExpr' u v s -> UExpr' (BF u) (BF v) s
markBF = cmapBV fromB . mapFV F

unmarkBF :: UExpr' (BF u) (BF v) s -> UExpr' u v s
unmarkBF = cmapBV B . mapFV fromF

abstract
  :: (F.Fresh v, Hashable v, Eq v)
  => v -> UExpr' (BF v) (BF v) s -> (v -> UExpr' (BF v) (BF v) s)
abstract targ e v = runFresh $ loop e
  where
    loop (UVar s (B u))
      | u == targ = return $ UVar s (B v)
      | otherwise = return $ UVar s (B u)
    loop (UVar s (F x)) = return $ UVar s (F x)
    loop (UPrimI s n) = return $ UPrimI s n
    loop (UApp s l r) = UApp s <$> loop l <*> loop r
    loop (UPrimOp s op l) = UPrimOp s op <$> loop l
    loop (UPrimBin s op l r) = UPrimBin s op <$> loop l <*> loop r
    loop (UIfte s p l r) = UIfte s <$> loop p <*> loop l <*> loop r
    loop (UFix s b) = UFix s <$> loop b
    loop (ULam s b) = do
      x <- fresh Nothing
      bdy <- loop $ b (B x)
      return $ ULam s $ abstract x bdy . fromB

instance (Hashable u, Eq u, F.Fresh u) => Foldable (UExpr' u v) where
  foldMap f = runFresh . loop
    where
      loop (UPrimI s _)       = return $ f s
      loop (UVar s _)         = return $ f s
      loop (UPrimOp s _ e)    = (f s <>) <$> loop e
      loop (UPrimBin s _ l r) = (f s <>) <$> getAp (foldMap (Ap . loop) [l, r])
      loop (UIfte s p t e) =
        (f s <>) <$> getAp (foldMap (Ap . loop) [p, t, e])
      loop (ULam s b) = do
        v <- fresh Nothing
        (f s <>) <$> loop (b v)
      loop (UFix s e) = (f s <>) <$> loop e
      loop (UApp s l r) =
        (f s <>) <$> getAp (foldMap (Ap . loop) [l, r])

type UExpr u v = UExpr' u v ()

data UTypeRep' v = UNatT | (UTypeRep' v) :-> (UTypeRep' v) | UVarT v
  deriving stock (Eq, Ord, Generic1)
  deriving stock (Functor, Foldable, Traversable)
  deriving anyclass (Hashable1)

pattern AnyVar :: v -> BF v
pattern AnyVar v <- (viewVar -> v)
{-# COMPLETE AnyVar #-}

viewVar :: BF p -> p
viewVar (B v) = v
viewVar (F v) = v

instance Show v => Show (UTypeRep' v) where
  showsPrec _ UNatT = showString "ℕ"
  showsPrec d (a :-> b) = showParen (d > 10) $
    showsPrec 11 a . showString " -> " . showsPrec 10 b
  showsPrec _ (UVarT v) = shows v

freshVar :: (Monad m, F.Fresh v, Hashable v, Eq v)
         => Maybe v -> FreshT v m (UTypeRep' v)
freshVar = fmap UVarT . fresh

infixr 0 :->

deriveEq1 ''UTypeRep'
deriveOrd1 ''UTypeRep'

instance Show1 UTypeRep' where
  liftShowsPrec _ _ _ UNatT      = showString "ℕ"
  liftShowsPrec sd _ d (UVarT v) = sd d v
  liftShowsPrec sd sl d (l :-> r) = showParen (d > 0) $
    liftShowsPrec sd sl 1 l . showString " -> " .
    liftShowsPrec sd sl 0 r

instance Matchable UTypeRep' where
  match = matchWithMetaVarCon @"UVarT"

instance Applicative UTypeRep' where
  pure = return
  (<*>) = ap

instance Monad UTypeRep' where
  return = UVarT
  UNatT >>= _ = UNatT
  (l :-> r) >>= f = (l >>= f) :-> (r >>= f)
  UVarT v >>= f = f v

instance Monad m => R.MonadReader r (RWST r w s m) where
  local = local
  ask   = ask

instance (Monoid w, Monad m) => W.MonadWriter w (RWST r w s m) where
  tell = tell
  listen = listen
  pass = pass

type ClosedUTypeRep = UTypeRep' Void
type UTypeRep = UTypeRep' Var
type TExpr u v = UExpr' u v UTypeRep
data InferenceError v =
    UnificationError (UnificationError UTypeRep' Var)
  | ElaborationError (ElaborationError v)
    deriving (Show, Eq, Ord, Typeable, Exception)

infer :: (Hashable v, Eq v, F.Fresh v)
      => UExpr v v -> Either (InferenceError v) (TExpr v v)
infer =
  uncurry solve
  <=< B.first ElaborationError . elaborate

getType :: TExpr u v -> UTypeRep
getType (UPrimI t _)       = t
getType (UVar t _)         = t
getType (UPrimOp t _ _)    = t
getType (UPrimBin t _ _ _) = t
getType (UIfte t _ _ _)    = t
getType (ULam t _)         = t
getType (UFix t _)         = t
getType (UApp t _ _)       = t

runRWST'
  :: (Eq v, Hashable v, Monad m)
  => RWST (HashMap v UTypeRep) (HashSet (Equation UTypeRep' Var)) () m a
  -> m (a, HashSet (Equation UTypeRep' Var))
runRWST' act = evalRWST act mempty ()

newtype ElaborationError v = NotInScope v
  deriving (Read, Show, Eq, Ord, Typeable, Exception)
instance MonadError e m => MonadError e (RWST r w s m) where
  throwError = lift . throwError
  catchError = liftCatch catchError

type Machine v =
  FreshT Var
    (FreshT v
      (RWST
        (HashMap v UTypeRep)
        (HashSet (Equation UTypeRep' Var))
        ()
        (Except (ElaborationError v))))

elaborate
  :: forall v. (Hashable v, Eq v, F.Fresh v)
  => UExpr v v
  -> Either
      (ElaborationError v)
      (TExpr v v, HashSet (Equation UTypeRep' Var))
elaborate
  = right (first unmarkBF)
  . runExcept
  . runRWST'
  . runFreshT
  . runFreshT . elab . markBF
  where
    elabWith ty a = do
      b <- elab a
      W.tell $ HS.singleton $ getType b %== ty
      return b
    elab :: UExpr (BF v) (BF v) -> Machine v (TExpr (BF v) (BF v))
    elab (UPrimI _ n)        = return $ UPrimI UNatT n
    elab (UVar _ (AnyVar v))          = do
      t <- maybe (throwError $ NotInScope v) return =<< R.asks (HM.lookup v)
      return $ UVar t (B v)
    elab (UPrimOp _ op a)    = UPrimOp UNatT op <$> elabWith UNatT a
    elab (UPrimBin _ op l r) =
      UPrimBin UNatT op <$> elabWith UNatT l <*> elabWith UNatT r
    elab (UIfte _ p t e) = do
      a <- freshVar (Just "#a")
      UIfte a
        <$> elabWith UNatT p
        <*> elabWith a t
        <*> elabWith a e
    elab (UFix _ b) = do
      a <- freshVar (Just "#α")
      UFix a <$> elabWith (a :-> a) b
    elab (UApp _ l r) = do
      b <- freshVar (Just "#b")
      a <- freshVar (Just "#a")
      UApp b <$> elabWith (a :-> b) l <*> elabWith a r
    elab (ULam _ bdy) = do
      a <- freshVar (Just "#a")
      b <- freshVar (Just "#b")
      let arr = a :-> b
      v <- lift $ fresh Nothing
      bdy' <- R.local (HM.insert v a) $ elabWith b $ bdy (B v)
      return $ ULam arr $ abstract v bdy' . fromB

solve
  :: TExpr v v
  -> HashSet (Equation UTypeRep' Var)
  -> Either (InferenceError v) (TExpr v v)
solve ex eqs =
  B.bimap UnificationError ((<$> ex) . substituteM) $
    unify (HS.toList eqs)
