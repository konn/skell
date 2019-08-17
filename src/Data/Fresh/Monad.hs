{-# LANGUAGE DerivingStrategies, FlexibleInstances             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances          #-}
module Data.Fresh.Monad
  ( FreshT, FreshM, Fresh,
    runFreshT, runFresh, runFreshWith, runFreshTWith,
    fresh, reserve, reserveMany,
    Var(..)
  ) where
import           Control.Monad.Except
import           Control.Monad.Reader.Class
import           Control.Monad.State.Strict
import           Control.Monad.Writer.Class
import           Data.Fresh                 hiding (fresh)
import qualified Data.Fresh                 as F
import           Data.Functor.Identity
import           Data.Hashable
import           Data.HashSet               (HashSet)
import qualified Data.HashSet               as HS
import           Data.Maybe

newtype FreshT v m a = FreshT { runFreshT_ :: StateT (HashSet v) m a }
  deriving newtype (Functor, Applicative, Monad, MonadTrans)

deriving newtype instance MonadReader e m => MonadReader e (FreshT v m)
deriving newtype instance MonadWriter e m => MonadWriter e (FreshT v m)
deriving newtype instance MonadError e m => MonadError e (FreshT v m)

type FreshM v = FreshT v Identity

runFreshT :: Monad m => FreshT v m a -> m a
runFreshT = flip evalStateT HS.empty . runFreshT_

runFresh :: FreshM v a -> a
runFresh = flip evalState HS.empty . runFreshT_

runFreshTWith
  :: (Hashable v, Eq v, Foldable t, Monad m)
  => t v
  -> FreshT v m a -> m a
runFreshTWith inp = flip evalStateT (foldMap HS.singleton inp) . runFreshT_

runFreshWith :: (Hashable v, Eq v, Foldable t) => t v -> FreshM v a -> a
runFreshWith inp = flip evalState (foldMap HS.singleton inp) . runFreshT_

fresh :: (Hashable v, Eq v, F.Fresh v, Monad m)
      => Maybe v -> FreshT v m v
fresh m = FreshT $ do
  v <- gets $ F.fresh $ fromMaybe F.origin m
  modify $ HS.insert v
  return v

reserve
  :: (Hashable v, Eq v, F.Fresh v, Monad m)
  => v -> FreshT v m ()
reserve = FreshT . modify . HS.insert

reserveMany
  :: (Foldable t, Hashable v, Eq v, F.Fresh v, Monad m)
  => t v -> FreshT v m ()
reserveMany = mapM_ reserve
