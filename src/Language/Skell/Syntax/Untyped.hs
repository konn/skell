{-# LANGUAGE DataKinds, DeriveAnyClass, DeriveFoldable, DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric, DeriveTraversable, DerivingVia            #-}
{-# LANGUAGE PatternSynonyms, TemplateHaskell, TypeApplications       #-}
{-# LANGUAGE TypeOperators                                            #-}
module Language.Skell.Syntax.Untyped where
import Control.Monad
import Data.Deriving
import Data.Hashable.Lifted
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

data UTypeRep' v = UNatT | (UTypeRep' v) :-> (UTypeRep' v) | UVarT v
  deriving stock (Read, Show, Eq, Ord, Generic1)
  deriving stock (Functor, Foldable, Traversable)
  deriving anyclass (Hashable1)
infixr 0 :->

deriveEq1 ''UTypeRep'
deriveShow1 ''UTypeRep'
deriveOrd1 ''UTypeRep'

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

type UTypeRep = UTypeRep' Void

