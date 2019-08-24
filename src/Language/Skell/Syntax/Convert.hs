{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs     #-}
{-# LANGUAGE LambdaCase, MultiParamTypeClasses, RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeApplications #-}
{-# LANGUAGE UndecidableInstances                                      #-}
module Language.Skell.Syntax.Convert where
import Data.Fresh.Monad
import Data.Hashable
import Data.Proxy
import Data.Void
import Language.Skell.Syntax         as Typed
import Language.Skell.Syntax.Untyped as Untyped
import Numeric.Natural
import Unsafe.Coerce

class ToTypeRep a where
  toTypeRepM
    :: (Fresh v, Hashable v, Eq v)
    => Proxy a
    -> FreshM v (UTypeRep' v)

instance ToTypeRep Natural where
  toTypeRepM _ = return UNatT

instance (ToTypeRep a, ToTypeRep b) => ToTypeRep (a -> b) where
  toTypeRepM _ = (:->) <$> toTypeRepM (Proxy @a) <*> toTypeRepM (Proxy @b)

untype
  :: Expr a (Id v) -> UExpr v
untype (Var (V v))      = UVar () v
untype (Var (In e))     = untype e
untype (PrimI n)        = UPrimI () n
untype (PrimOp op l)    = UPrimOp () op (untype l)
untype (PrimBin op l r) = UPrimBin () op (untype l) (untype r)
untype (Ifte p t e)     =
  UIfte () (untype p) (untype t) (untype e)
untype (Fix a) = UFix () (untype a)
untype (App l r) = UApp () (untype l) (untype r)
untype (Lam b) = ULam () $ untype . b . V

data SomeTyped  u v where
  SomeTypedE :: ExprF a u v -> SomeTyped  u v

deriving instance
  (Fresh v, Hashable v, Eq v, Show v) => Show (SomeTyped (Id v) (Id v))

promote
  :: forall u. UExpr' u u (UTypeRep' Void) -> SomeTyped (Id u) (Id u)
promote (UPrimI _ i) = SomeTypedE $ PrimI i
promote (UVar t v)   =
  case promoteTy t of
    SomeTR (_ :: TypeRep a) -> SomeTypedE $ Var (V v :: Id u a)
promote (UPrimOp _ op l0) =
  case promote l0 of
    SomeTypedE l -> SomeTypedE $ PrimOp op $ unsafeCoerce l
promote (UPrimBin _ bin l0 r0) =
  case (promote l0, promote r0) of
    (SomeTypedE l, SomeTypedE r) ->
      SomeTypedE $ PrimBin bin (unsafeCoerce l) (unsafeCoerce r)
promote (UIfte ty p0 l0 r0) =
  case (promoteTy ty, promote p0, promote l0, promote r0) of
    (SomeTR (_ :: TypeRep a), SomeTypedE p, SomeTypedE l, SomeTypedE r) ->
      SomeTypedE $ Ifte @_  @_ @a (unsafeCoerce p) (unsafeCoerce l) (unsafeCoerce r)
promote (UApp b l0 r0) =
  case (promoteTy (getType r0), promoteTy b, promote l0, promote r0) of
    (SomeTR (_ :: TypeRep a), SomeTR (_ :: TypeRep b), SomeTypedE l, SomeTypedE r) ->
      SomeTypedE $
        App
        (unsafeCoerce l :: ExprF (a -> b) (Id u) (Id u)) (unsafeCoerce r)
promote (UFix a b) =
  case (promoteTy a, promote b) of
    (SomeTR (_ :: TypeRep a), SomeTypedE bdy) ->
      SomeTypedE $ Fix @a (unsafeCoerce bdy)
promote (ULam ~(a :-> b) f) =
  case (promoteTy a, promoteTy b) of
    (SomeTR (_ :: TypeRep a), SomeTR (_ :: TypeRep b)) ->
      SomeTypedE $ Lam @a @_ @b  $ \case
        In e -> case promote $ f =<<< (a <$ untype e) of
          SomeTypedE te -> unsafeCoerce te
        V v -> case promote $ f v of
          SomeTypedE te -> unsafeCoerce te

promoteTy :: UTypeRep' Void -> SomeTypeRep
promoteTy UNatT = SomeTR NatT
promoteTy (a :-> b) =
  case (promoteTy a, promoteTy b) of
    (SomeTR l, SomeTR r) -> SomeTR $ ArrT l r
promoteTy (UVarT v) = absurd v
