{-# LANGUAGE FlexibleInstances, GADTs, LambdaCase, LiberalTypeSynonyms #-}
{-# LANGUAGE RankNTypes, TypeOperators                                 #-}
module Language.Skell.Eval where
import           Data.Hashable
import           Data.HEnv
import qualified Data.HEnv                        as Env
import           Language.Skell.Syntax
import           Math.NumberTheory.Powers.Squares
import           Numeric.Natural

eval :: (Show v, Eq v, Hashable v, HEnvLookup v a)
     => HEnv v -> Expr a (Id v) -> Either String (View v a)
eval _   (PrimI i)        = return $ I i
eval env (Var (V v))      =
  maybe (Left $ "Variable not in scope: " <> show v) Right $
  Env.lookup v env
eval env (Var (In v))     = eval env v
eval env (PrimOp op l)    = I . evalOp op . unI <$> eval env l
eval env (Ifte p t f)     = eval env p >>= \case
  I i ->
    if i == 0
    then eval env t
    else eval env f
eval env (PrimBin op l r) =
  (I .) . evalBin op <$> (unI <$> eval env l) <*> (unI <$> eval env r)
eval _   (Lam b)          = return $ L b
eval env (App l r) = eval env l >>= \case
  L b -> eval env . b . In . fromView =<< eval env r
eval env (Fix b) = eval env b >>= \case
  L f -> eval env $ f (In $ Fix b)

unpairWord :: Natural -> (Natural, Natural)
unpairWord z =
  let w = (integerSquareRoot' (8 * z + 1) - 1) `div` 2
      t = (w*w + w) `div` 2
      p@(_, y) = (w - y, z - t)
  in p

pair :: Natural -> Natural -> Natural
pair k1 k2 = (k1 + k2) * (k1 + k2 + 1) `div` 2 + k2

evalOp :: PrimOp -> Natural -> Natural
evalOp Fst    = fst . unpairWord
evalOp Snd    = snd . unpairWord
evalOp IsZero = \i -> if i == 0 then 0 else 1

evalBin :: PrimBin -> Natural -> Natural -> Natural
evalBin Add  = (+)
evalBin Sub  = (max 0 .) . (-)
evalBin Mul  = (*)
evalBin Div  = div
evalBin Mod  = mod
evalBin Pair = pair
evalBin Eql  = \l r -> if l == r then 0 else 1
evalBin Lt   = \l r -> if l < r then 0 else 1
