{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds         #-}
{-# LANGUAGE DerivingStrategies, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, MultiParamTypeClasses, PolyKinds, RankNTypes     #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, TypeFamilies     #-}
{-# LANGUAGE TypeOperators, UndecidableInstances                     #-}
module Data.TypeLevel.Path.Parametric where
import Data.Kind
import Data.Proxy
import GHC.Generics
import GHC.TypeLits

data ParPath f where
  M   :: ParPath f -> ParPath (M1 i c f)
  InL :: ParPath f -> ParPath (f :+: g)
  InR :: ParPath g -> ParPath (f :+: g)
  P   :: ParPath Par1

class KnownParPath f (p :: ParPath f) where
  parPath :: proxy p -> ParPath f

instance KnownParPath Par1 'P where
  parPath = const P

instance KnownParPath f p => KnownParPath (f :+: g) ('InL p) where
  parPath = const $ InL $ parPath $ Proxy @p

instance KnownParPath g q => KnownParPath (f :+: g) ('InR q) where
  parPath = const $ InR $ parPath $ Proxy @q

instance KnownParPath f p => KnownParPath (M1 i c f) ('M p) where
  parPath = const $ M $ parPath $ Proxy @p

walkParPath
  :: Generic1 f
  => ParPath (Rep1 f) -> f a -> Maybe a
walkParPath p = walkParPathG p . from1

walkParPathG :: ParPath f -> f a -> Maybe a
walkParPathG (M p)   (M1 f)   = walkParPathG p f
walkParPathG (InL p) (L1 f)   = walkParPathG p f
walkParPathG (InL _) (R1 _)   = Nothing
walkParPathG (InR p) (R1 f)   = walkParPathG p f
walkParPathG (InR _) (L1 _)   = Nothing
walkParPathG P       (Par1 a) = Just a

type family FromJust msg (a :: Maybe k) :: k where
  FromJust msg 'Nothing  = TypeError msg
  FromJust _   ('Just k) = k

type Cons1Path  s f =
  (FromJust
    ('Text "A type "
      ':<>: 'ShowType f
      ':<>: 'Text " doesn't have a unary constructor with name "
      ':<>: 'ShowType s ':<>: 'Text ".")
    (Cons1PathM s f) :: ParPath (Rep1 f))

type Cons1PathM s f =
  (Cons1Path' s (Rep1 f) :: Maybe (ParPath (Rep1 f)))

type family Cons1Path' s f :: Maybe (ParPath f) where
  Cons1Path' s (D1 _ f) = 'M <$> Cons1Path' s f
  Cons1Path' s (l :+: r) = 'InL <$> Cons1Path' s l <|> 'InR <$> Cons1Path' s r
  Cons1Path' s (C1 ('MetaCons s _ _) f) = 'M <$> GetParPath' f
  Cons1Path' _ _ = 'Nothing

type GetParPath (f :: * -> *) = (GetParPath' (Rep1 f) :: Maybe (ParPath (Rep1 f)))

type family GetParPath' f :: Maybe (ParPath f) where
  GetParPath' Par1 = 'Just 'P
  GetParPath' (C1 _ f) = 'M <$> GetParPath' f
  GetParPath' (S1 _ f) = 'M <$> GetParPath' f
  GetParPath' _        = 'Nothing

type family FromBool (msg :: ErrorMessage) (b :: Bool) :: Constraint where
  FromBool _ 'True  = ()
  FromBool m 'False = TypeError m

type family (||) (a :: Bool) (b :: Bool) :: Bool where
  'True  || _ = 'True
  'False || a = a

type family IsJust (a :: Maybe k) :: Bool where
  IsJust 'Nothing  = 'False
  IsJust ('Just _) = 'True

type HasCons1 s t = KnownParPath (Rep1 t) (Cons1Path s t)


type family (<|>) (l :: Maybe a) (r :: Maybe a) :: Maybe a where
  'Nothing <|> t = t
  'Just a  <|> _ = 'Just a
infixl 3 <|>

type family (<$>) (f :: a -> b) (ma :: Maybe a) :: Maybe b where
  _ <$> 'Nothing = 'Nothing
  f <$> 'Just a  = 'Just (f a)
infixl 4 <$>
