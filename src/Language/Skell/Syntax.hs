{-# LANGUAGE DataKinds, DerivingStrategies, FlexibleInstances, GADTs #-}
{-# LANGUAGE LiberalTypeSynonyms, PatternSynonyms, PolyKinds         #-}
{-# LANGUAGE QuantifiedConstraints, RankNTypes, ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving, TypeApplications, TypeOperators     #-}
{-# LANGUAGE ViewPatterns                                            #-}
module Language.Skell.Syntax where
import           Control.Indexed
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Orphans          ()
import qualified Control.Monad.Trans.Writer.CPS as W
import           Control.Monad.Writer.Class
import           Data.Either
import qualified Data.Foldable                  as F
import           Data.Fresh
import           Data.Fresh.Monad
import           Data.Hashable
import           Data.HashSet                   (HashSet)
import qualified Data.HashSet                   as HS
import           Data.Maybe
import           Data.Proxy
import           Data.String
import           Data.Type.Equality
import           Numeric.Natural

data ExprF a u v where
  PrimI   :: Natural -> ExprF Natural u v
  Var     :: HasTypeRep a => v a -> ExprF a u v
  PrimOp  :: PrimOp -> ExprF Natural u v -> ExprF Natural u v
  PrimBin :: PrimBin -> ExprF Natural u v -> ExprF Natural u v -> ExprF Natural u v
  Ifte    :: ExprF Natural u v -> ExprF a u v -> ExprF a u v -> ExprF a u v
  Lam     :: HasTypeRep a => (u a -> ExprF b u v) -> ExprF (a -> b) u v
  Fix     :: ExprF (a -> a) u v -> ExprF a u v
  App     :: ExprF (a -> b) u v -> ExprF a u v -> ExprF b u v

data TypeRep a where
  NatT :: TypeRep Natural
  ArrT :: TypeRep a -> TypeRep b -> TypeRep (a -> b)
deriving instance Show (TypeRep a)

instance TestEquality TypeRep where
  testEquality NatT NatT = Just Refl
  testEquality (ArrT s1 e1) (ArrT s2 e2) = do
    Refl <- testEquality s1 s2
    Refl <- testEquality e1 e2
    return Refl
  testEquality _    _ = Nothing

class HasTypeRep a where
  typeRepOf :: p a -> TypeRep a

instance HasTypeRep Natural where
  typeRepOf = const NatT

instance (HasTypeRep a, HasTypeRep b) => HasTypeRep (a -> b) where
  typeRepOf = const $ ArrT (typeRepOf $ Proxy @a) (typeRepOf $ Proxy @b)

lam :: HasTypeRep a => (Expr a v -> Expr b v) -> Expr (a -> b) v
lam f = Lam $ f . Var

instance Num (ExprF Natural u v) where
  fromInteger = PrimI . fromInteger
  (+) = PrimBin Add
  (-) = PrimBin Sub
  (*) = PrimBin Mul
  abs = error "abs for Expr"
  signum = error "Signum for Expr"

data PrimOp = Fst | Snd | IsZero deriving (Read, Show, Eq, Ord)
data PrimBin
  = Add | Sub | Mul | Div | Mod
  | Pair | Eql | Lt deriving (Read, Show, Eq, Ord)

instance IProfunctor (ExprF a) where
  idimap _ _ (PrimI i)        = PrimI i
  idimap _ g (Var v)          = Var $ g v
  idimap f g (PrimOp op a)    = PrimOp op (idimap f g a)
  idimap f g (PrimBin op a b) = PrimBin op (idimap f g a) (idimap f g b)
  idimap f g (Lam b)          = Lam (idimap f g . b . f)
  idimap f g (Ifte p t e)     = Ifte (idimap f g p) (idimap f g t) (idimap f g e)
  idimap f g (App l r)        = App (idimap f g l) (idimap f g r)
  idimap f g (Fix b)          = Fix (idimap f g b)

support
  :: forall b v.
     (Fresh v, Hashable v, Eq v)
  => Expr b (Id v) -> HashSet v
support = W.execWriter . runFreshT . loop . aging
  where
    loop :: Expr a (Age (Id v)) -> FreshT v (W.Writer (HashSet v)) ()
    loop (Var agv)         =
      case agv of
        (Old (V v))       -> tell $ HS.singleton v
        (unAge -> (In e)) -> loop $ aging e
        _                 -> return ()
    loop PrimI{}         = return ()
    loop (PrimOp _ l)    = loop l
    loop (PrimBin _ l r) = loop l >> loop r
    loop (Ifte p t e)    = loop p >> loop t >> loop e
    loop (App l r)       = loop l >> loop r
    loop (Fix l)         = loop l
    loop (Lam b) = do
      v <- freshM Nothing
      loop $ b $ New $ V v

type Expr a v = ExprF a v v
data Id v a = In { out :: Expr a (Id v) }
            | V v

data View v a where
  I :: { unI :: Natural } -> View v Natural
  L :: HasTypeRep a => (Id v a -> Expr b (Id v)) -> View v (a -> b)

fromView :: HasTypeRep a => View v a -> Expr a (Id v)
fromView (I a) = PrimI a
fromView (L b) = Lam b

instance (Hashable v, Eq v, Fresh v, Show v) => Show (Expr a (Id v)) where
  showsPrec _ a = runFreshWith (support a) $ showM a

showM :: (Fresh v, Hashable v, Eq v, Show v) => Expr a (Id v) -> FreshM v ShowS
showM (PrimI i)    = return $ shows i
showM (Var (In e)) = showM e
showM (Var (V v))  = return (shows v)
showM (Fix b) = do
  sb <- showM b
  return $ showString "(fix " . sb . showChar ')'
showM (PrimOp op l) = do
  lb <- showM l
  return $ showChar '(' . prettyOp op . showChar ' ' . lb . showChar ')'
showM (PrimBin op l r) = do
  lb <- showM l
  rb <- showM r
  return $ showChar '(' . prettyBin op
    . showChar ' ' . lb
    . showChar ' ' . rb
    . showChar ')'
showM (App l r) = do
  lb <- showM l
  rb <- showM r
  return $
    showString "(" . lb . showChar ' '
    . rb . showChar ')'
showM (Ifte p t e) = do
  pb <- showM p
  tb <- showM t
  eb <- showM e
  return $
    showString "(if " . pb
    . showChar ' ' . tb
    . showChar ' ' . eb . showChar ')'
showM (Lam bdy) = do
  v <- freshM Nothing
  b <- showM $ bdy $ V v
  return $
    showString "(lam [" . shows v . showString "] " . b . showChar ')'

prettyOp :: PrimOp -> ShowS
prettyOp Fst    = showString "fst"
prettyOp Snd    = showString "snd"
prettyOp IsZero = showString "is-zero"

prettyBin :: PrimBin -> ShowS
prettyBin Add  = showString "+"
prettyBin Sub  = showString "-"
prettyBin Mul  = showString "*"
prettyBin Pair = showString "pair"
prettyBin Eql  = showString "="
prettyBin Lt   = showString "<"
prettyBin Mod  = showString "mod"
prettyBin Div  = showString "div"

instance (Show v, Hashable v, Eq v, Fresh v) => Show (View v a) where
  showsPrec d (I i) = showsPrec d i
  showsPrec d (L b) = showsPrec d $ Lam b

data Age v a = New (v a) | Old (v a)
  deriving (Read, Show, Eq, Ord)

unAge :: Age v a -> v a
unAge (New va) = va
unAge (Old va) = va

instance IsString v => IsString (Id v a) where
  fromString = V . fromString

instance Fresh v => Fresh (Id v a) where
  origin = V origin
  fresh i =
      V . fresh (fromMaybe origin $ fromV i)
    . mapMaybe fromV . F.toList

instance IsString (v a) => IsString (Age v a) where
  fromString = New . fromString

instance Fresh (v a) => Fresh (Age v a) where
  origin = New origin
  fresh i = New . fresh (unAge i) . map unAge . F.toList

fromV :: Id v a -> Maybe v
fromV (V a) = Just a
fromV _     = Nothing

pattern AnyAge :: v a -> Age v a
pattern AnyAge v <- (unAge -> v)
{-# COMPLETE AnyAge #-}

data SomeVar v where
  SomeVar :: Fresh (v a) => v a -> SomeVar v

aging :: Expr a (Id v) -> Expr a (Age (Id v))
aging = idimap unAge Old

data SomeTypeRep where
  SomeTR :: HasTypeRep a => TypeRep a -> SomeTypeRep
deriving instance Show SomeTypeRep

data AbstractionError v = TyVarMismatch v SomeTypeRep
  deriving (Show)

abstract
  :: forall v b a. (Eq v, Hashable v, Fresh v, HasTypeRep a)
  => v -> Expr b (Id v) -> Either (AbstractionError v) (Id v a -> Expr b (Id v))
abstract old e0 = runExcept $ runFreshTWith (support e0) $ loop $ aging e0
  where
    aRep = typeRepOf (Proxy @a)
    loop
      :: Expr x (Age (Id v))
      -> FreshT v (Except (AbstractionError v)) (Id v a -> Expr x (Id v))
    loop (PrimI n) = return $ const $ PrimI n
    loop (Var (Old idu@(V u))) =
      case testEquality (typeRepOf idu) aRep of
        Just Refl | u == old -> return Var
        Nothing
          | u == old -> throwError $ TyVarMismatch u (SomeTR $ typeRepOf idu)
        _                    -> return $ const $ Var idu
    loop (Var (AnyAge (V v))) = return $ const $ Var $ V v
    loop (Var (AnyAge (In i))) = loop $ aging i
    loop (PrimOp b e) = fmap (PrimOp b) <$> loop e
    loop (PrimBin b l r) = liftM2 (PrimBin b) <$> loop l <*> loop r
    loop (App l r) = liftM2 App <$> loop l <*> loop r
    loop (Fix b) = fmap Fix <$> loop b
    loop (Ifte p t e) = liftM3 Ifte <$> loop p <*> loop t <*> loop e
    loop (Lam b) = do
      bound <- freshM Nothing
      b' <- loop $ b $ New $ V bound
      return $ \new -> Lam $
        fromRight (error "Abstraction failure: impossible rebinding!") $
        abstract bound $ b' new

