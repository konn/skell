{-# LANGUAGE FlexibleInstances, GADTs, LiberalTypeSynonyms, RankNTypes #-}
{-# LANGUAGE TypeOperators                                             #-}
module Language.Skell.Syntax where
import Control.Indexed
import Control.Monad.State.Strict
import Data.Fresh
import Numeric.Natural

data ExprF a u v where
  PrimI   :: Natural -> ExprF Natural u v
  Var     :: v a -> ExprF a u v
  PrimOp  :: PrimOp -> ExprF Natural u v -> ExprF Natural u v
  PrimBin :: PrimBin -> ExprF Natural u v -> ExprF Natural u v -> ExprF Natural u v
  Ifte    :: ExprF Natural u v -> ExprF a u v -> ExprF a u v -> ExprF a u v
  Lam     :: (u a -> ExprF b u v) -> ExprF (a -> b) u v
  Fix     :: ExprF (a -> a) u v -> ExprF a u v
  App     :: ExprF (a -> b) u v -> ExprF a u v -> ExprF b u v

lam :: (Expr a v -> Expr b v) -> Expr (a -> b) v
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

type Expr a v = ExprF a v v
data Id v a = In { out :: Expr a (Id v) }
            | V v

data View v a where
  I :: { unI :: Natural } -> View v Natural
  L :: (Id v a -> Expr b (Id v)) -> View v (a -> b)

fromView :: View v a -> Expr a (Id v)
fromView (I a) = PrimI a
fromView (L b) = Lam b

instance (Fresh v, Show v) => Show (Expr a (Id v)) where
  showsPrec _ a = evalState (showM a) []

showM :: (Fresh v, Show v) => Expr a (Id v) -> State [v] ShowS
showM (PrimI i)    = return $ shows i
showM (Var (In e)) = showM e
showM (Var (V v))  = modify (v:) >> return (shows v)
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
  vars <- get
  let v = fresh origin vars
  modify (v:)
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
prettyBin Mul  = showString "is-*"
prettyBin Pair = showString "pair"
prettyBin Eql  = showString "="
prettyBin Lt   = showString "<"
prettyBin Mod  = showString "mod"
prettyBin Div  = showString "div"

abstract :: (Eq v) => v -> Expr b (Id v) -> (Id v a -> Expr b (Id v))
abstract = undefined

instance (Show v, Fresh v) => Show (View v a) where
  showsPrec d (I i) = showsPrec d i
  showsPrec d (L b) = showsPrec d $ Lam b
