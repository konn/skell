{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric           #-}
{-# LANGUAGE DeriveTraversable, DerivingStrategies, PatternSynonyms #-}
module Language.Skell.Syntax.Untyped where
import Control.Monad
import Data.Unification.Generic
import Data.Void
import GHC.Generics
import Language.Skell.Syntax
import Numeric.Natural

data UExpr' s u v
  = UPrimI s Natural
  | UVar s v
  | UPrimOp s PrimOp (UExpr' s u v)
  | UPrimBin PrimBin (UExpr' s u v) (UExpr' s u v)
  | UIfte (UExpr' s u v) (UExpr' s u v) (UExpr' s u v)
  | ULam (u -> UExpr' s u v)
  | UFix (UExpr' s u v)
  | UApp (UExpr' s u v) (UExpr' s u v)

type UExpr = UExpr' ()

data UTypeRep' v = UNatT | UArrT (UTypeRep' v) (UTypeRep' v) | UVarT v
  deriving (Read, Show, Eq, Ord, Generic1)
  deriving (Functor, Foldable, Traversable)

instance Applicative UTypeRep' where
  pure = return
  (<*>) = ap

instance Monad UTypeRep' where
  return = UVarT
  UNatT >>= _ = UNatT
  (UArrT l r) >>= f = UArrT (l >>= f) (r >>= f)
  UVarT v >>= f = f v

type UTypeRep = UTypeRep' Void

instance Matchable UTypeRep' where
  match (UVarT a)   (UVarT b) = Just [a :== UVarT b]
  match (UVarT a)   ty        = Just [a :== ty]
  match ty          (UVarT a) = Just [a :== ty]
  match UNatT       UNatT     = Just []
  match (UArrT l r) (UArrT l' r') =
    (++) <$> match l l'  <*> match r r'
  match UArrT{} UNatT{} = Nothing
  match UNatT{} UArrT{} = Nothing
