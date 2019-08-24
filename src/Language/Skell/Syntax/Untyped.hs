{-# LANGUAGE DataKinds, DeriveAnyClass, DeriveFoldable, DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric, DeriveTraversable, DerivingVia                 #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, LambdaCase               #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms, RankNTypes, ScopedTypeVariables              #-}
{-# LANGUAGE TemplateHaskell, TypeApplications, TypeOperators              #-}
{-# LANGUAGE UndecidableInstances, ViewPatterns                            #-}
module Language.Skell.Syntax.Untyped
  ( module Language.Skell.Syntax.Untyped
  , PrimBin(..), PrimOp(..)
  ) where
import           Control.Exception              (Exception)
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Orphans          ()
import qualified Control.Monad.Reader.Class     as R
import           Control.Monad.Trans.RWS.CPS
import           Control.Monad.Trans.Writer.CPS (Writer, execWriter)
import qualified Control.Monad.Writer.Class     as W
import qualified Data.Bifunctor                 as B
import           Data.Bifunctor.TH
import           Data.Deriving
import qualified Data.Fresh                     as F
import           Data.Fresh.Monad
import           Data.Functor.Classes
import           Data.Hashable
import           Data.Hashable.Lifted
import           Data.HashMap.Strict            (HashMap)
import qualified Data.HashMap.Strict            as HM
import           Data.HashSet                   (HashSet)
import qualified Data.HashSet                   as HS
import           Data.Typeable
import           Data.Unification.Generic
import           Data.Void
import           GHC.Generics
import           Language.Skell.Syntax          hiding (abstract, support)
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
        v <- freshM Nothing
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
markBF = cmapBV viewVar . mapFV F

unmarkBF :: UExpr' (BF u) (BF v) s -> UExpr' u v s
unmarkBF = cmapBV B . mapFV viewVar


supportWith
  :: forall u v s.
     (Fresh v, Hashable v, Eq v)
  => (v -> u) -> (u -> HashSet v) -> UExpr' u u s -> HashSet v
supportWith fromUV toUV = execWriter . runFreshT . loop . markBF
  where
    loop :: UExpr' (BF u) (BF u) s -> FreshT v (Writer (HashSet v)) ()
    loop (UVar _ agv)         =
      case agv of
        (F v) -> W.tell $ toUV v
        _     -> return ()
    loop UPrimI{}           = return ()
    loop (UPrimOp _ _ l)    = loop l
    loop (UPrimBin _ _ l r) = loop l >> loop r
    loop (UIfte _ p t e)    = loop p >> loop t >> loop e
    loop (UApp _ l r)       = loop l >> loop r
    loop (UFix _ l)         = loop l
    loop (ULam _ b) = do
      v <- freshM Nothing
      loop $ b $ B $ fromUV v

support :: (Fresh v, Hashable v, Eq v) => UExpr' v v s -> HashSet v
support = supportWith id HS.singleton

abstract
  :: (F.Fresh v, Hashable v, Eq v)
  => v -> UExpr' v v s -> (v -> UExpr' v v s)
abstract targ e v = runFreshWith (support e) $ loop e
  where
    loop (UVar s u)
      | u == targ = return $ UVar s v
      | otherwise = return $ UVar s u
    loop (UPrimI s n) = return $ UPrimI s n
    loop (UApp s l r) = UApp s <$> loop l <*> loop r
    loop (UPrimOp s op l) = UPrimOp s op <$> loop l
    loop (UPrimBin s op l r) = UPrimBin s op <$> loop l <*> loop r
    loop (UIfte s p l r) = UIfte s <$> loop p <*> loop l <*> loop r
    loop (UFix s b) = UFix s <$> loop b
    loop (ULam s b) = do
      x <- freshM Nothing
      bdy <- loop $ b x
      return $ ULam s $ abstract x bdy

type UExpr v = UExpr' v v ()

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
freshVar = fmap UVarT . freshM

data UId v a = UV v | UIn (UExpr' (UId v a) (UId v a) a)
infixr 0 :->

(=<<<)
  :: (v -> UExpr' v v a)
  -> UExpr' v v a
  -> UExpr' v v a
infixr 1 =<<<
f =<<< UVar _ a = f a
_ =<<< UPrimI s a = UPrimI s a
f =<<< UPrimOp s op l = UPrimOp s op (f =<<< l)
f =<<< UPrimBin s op l r = UPrimBin s op (f =<<< l) (f =<<< r)
f =<<< UIfte s p t e = UIfte s (f =<<< p) (f =<<< t) (f =<<< e)
f =<<< UFix s a = UFix s (f =<<< a)
f =<<< UApp s l r = UApp s (f =<<< l) (f =<<< r)
f =<<< ULam s b = ULam s ((f =<<<) . b)

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

type ClosedUTypeRep = UTypeRep' Void
type UTypeRep = UTypeRep' Var
type TExpr v = UExpr' v v UTypeRep
data InferenceError v =
    UnificationError (UnificationError UTypeRep' Var)
  | ElaborationError (ElaborationError v)
    deriving (Show, Eq, Ord, Typeable, Exception)

infer :: (Hashable v, Eq v, F.Fresh v)
      => UExpr v -> Either (InferenceError v) (TExpr v)
infer =
  uncurry solve
  <=< B.first ElaborationError . elaborate

getType :: UExpr' u v (UTypeRep' w) -> UTypeRep' w
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
  => UExpr v
  -> Either
      (ElaborationError v)
      (TExpr v, HashSet (Equation UTypeRep' Var))
elaborate
  = runExcept
  . runRWST'
  . runFreshT
  . runFreshT . elab
  where
    elabWith ty a = do
      b <- elab a
      W.tell $ HS.singleton $ getType b %== ty
      return b
    elab :: UExpr v -> Machine v (TExpr v)
    elab (UPrimI _ n)        = return $ UPrimI UNatT n
    elab (UVar _ v)          = do
      t <- maybe (throwError $ NotInScope v) return =<< R.asks (HM.lookup v)
      return $ UVar t v
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
      v <- lift $ freshM Nothing
      bdy' <- R.local (HM.insert v a) $ elabWith b $ bdy v
      return $ ULam arr $ abstract v bdy'

solve
  :: TExpr v
  -> HashSet (Equation UTypeRep' Var)
  -> Either (InferenceError v) (TExpr v)
solve ex eqs =
  B.bimap UnificationError ((<$> ex) . substituteM) $
    unify (HS.toList eqs)

instance Num (UExpr' v u ()) where
  (+) = UPrimBin () Add
  (*) = UPrimBin () Mul
  negate = error "Negating UExpr"
  abs = error "Absing UExpr"
  fromInteger = UPrimI () . fromInteger
  signum = error "Signum UExpr"

toClosedTy
  :: UTypeRep' v -> Maybe (UTypeRep' Void)
toClosedTy UVarT{}   = Nothing
toClosedTy UNatT     = return UNatT
toClosedTy (a :-> b) = (:->) <$> toClosedTy a <*> toClosedTy b

instance (Fresh v, Hashable v, Eq v) => Fresh (UId v s) where
  origin = UV F.origin
  fresh uv ts0 =
    let ts = foldMap uidSupport ts0
    in UV $ F.fresh (fromUV F.origin uv) ts

fromUV :: p -> UId p a -> p
fromUV _ (UV v) = v
fromUV v _      = v

uidSupport
  :: (Hashable v, Fresh v, Eq v)
  => UId v s -> HS.HashSet v
uidSupport = loop
  where
    loop (UV v)  = HS.singleton v
    loop (UIn e) = supportWith UV loop e
