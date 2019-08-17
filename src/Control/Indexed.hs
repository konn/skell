{-# LANGUAGE DataKinds, GADTs, PolyKinds, RankNTypes, TypeOperators #-}
module Control.Indexed where

type a ~> b = forall (x :: k). a x -> b x
infixr 0 ~>

class IProfunctor p where
  idimap :: (u' ~> u) -> (v ~> v') -> p u v -> p u' v'
  ilmap  :: (u' ~> u) -> p u v -> p u' v
  ilmap f = idimap f id
  irmap :: (v ~> v')  -> p u v -> p u v'
  irmap = idimap id
