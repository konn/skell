{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Control.Monad.Orphans () where
import           Control.Monad.Except
import qualified Control.Monad.Reader.Class     as R
import qualified Control.Monad.Trans.RWS.CPS    as RWS
import qualified Control.Monad.Trans.Writer.CPS as WCPS
import qualified Control.Monad.Writer.Class     as W

instance Monad m => R.MonadReader r (RWS.RWST r w s m) where
  local = RWS.local
  ask   = RWS.ask

instance (Monoid w, Monad m) => W.MonadWriter w (RWS.RWST r w s m) where
  tell   = RWS.tell
  listen = RWS.listen
  pass   = RWS.pass

instance MonadError e m => MonadError e (RWS.RWST r w s m) where
  throwError = lift . throwError
  catchError = RWS.liftCatch catchError

instance (Monoid w, Monad m) => W.MonadWriter w (WCPS.WriterT w m) where
  tell   = WCPS.tell
  listen = WCPS.listen
  pass   = WCPS.pass

instance MonadError e m => MonadError e (WCPS.WriterT e m) where
  throwError = lift . throwError
  catchError = WCPS.liftCatch catchError
