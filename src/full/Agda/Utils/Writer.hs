{-# LANGUAGE CPP                  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The writer monad (transformer) to be used in Agda.
--
--   We use the CPS variant from @transformers@, which does not leak
--   space like the lazy (and the so-called strict) writer from
--   "Control.Monad.Writer".  See issue #8229.
--
--   Import this module instead of "Control.Monad.Writer".
--   Note that the CPS writer has no data constructor:
--   use 'writerT' and 'runWriterT' instead of @WriterT@ and its field.
--
--   For hot code with a single, strict accumulator, see also
--   "Agda.Utils.StrictWriter".

module Agda.Utils.Writer
  ( -- * The writer monad
    Writer, runWriter, execWriter, mapWriter
    -- * The writer monad transformer
  , WriterT, writerT, runWriterT, execWriterT, mapWriterT
    -- * The writer class
  , MonadWriter(..), listens, censor
  ) where

import Control.Monad.Trans.Control ( MonadTransControl(..) )
import Control.Monad.Trans.Writer.CPS
  ( Writer, runWriter, execWriter, mapWriter
  , WriterT, writerT, runWriterT, execWriterT, mapWriterT
  )
import Control.Monad.Writer.Class ( MonadWriter(..), listens, censor )

---------------------------------------------------------------------------
-- monad-control (as of 1.0.3.1) has no instance for the CPS writer.
-- This mirrors its instance for the lazy writer.

instance Monoid w => MonadTransControl (WriterT w) where
  type StT (WriterT w) a = (a, w)
  liftWith f = writerT $ (, mempty) <$> f runWriterT
  restoreT   = writerT
  {-# INLINABLE liftWith #-}
  {-# INLINABLE restoreT #-}

#if !MIN_VERSION_mtl(2,3,0)
import Control.Monad.Except ( MonadError(..) )
import Control.Monad.Reader ( MonadReader(..) )
import Control.Monad.State  ( MonadState(..) )
import Control.Monad.Trans  ( lift )

import Control.Monad.Trans.Writer.CPS qualified as CPS

---------------------------------------------------------------------------
-- mtl-2.3 ships these instances for the CPS writer, older mtl does not.

instance (Monoid w, Monad m) => MonadWriter w (CPS.WriterT w m) where
  writer = CPS.writer
  tell   = CPS.tell
  listen = CPS.listen
  pass   = CPS.pass

instance (Monoid w, MonadReader r m) => MonadReader r (CPS.WriterT w m) where
  ask    = lift ask
  local  = CPS.mapWriterT . local
  reader = lift . reader

instance (Monoid w, MonadState s m) => MonadState s (CPS.WriterT w m) where
  get   = lift get
  put   = lift . put
  state = lift . state

instance (Monoid w, MonadError e m) => MonadError e (CPS.WriterT w m) where
  throwError = lift . throwError
  catchError = CPS.liftCatch catchError
#endif
