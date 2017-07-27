{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Debug where

import Control.Applicative
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Writer

import Data.Maybe
import Data.Semigroup (Semigroup, Monoid, (<>), mempty, mappend, Any(..))
import Data.Traversable

import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options

import Agda.Interaction.Response

import Agda.Utils.Except
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty

#include "undefined.h"
import Agda.Utils.Impossible

class (Functor m, Applicative m, Monad m) => MonadDebug m where
  displayDebugMessage :: Int -> String -> m ()
  displayDebugMessage n s = traceDebugMessage n s $ return ()

  traceDebugMessage :: Int -> String -> m a -> m a
  traceDebugMessage n s cont = displayDebugMessage n s >> cont

  formatDebugMessage  :: VerboseKey -> Int -> TCM Doc -> m String

instance (MonadIO m) => MonadDebug (TCMT m) where

  displayDebugMessage n s = liftTCM $ do
    cb <- gets $ stInteractionOutputCallback . stPersistentState
    liftIO $ cb (Resp_RunningInfo n s)

  formatDebugMessage k n d = liftTCM $
    show <$> d `catchError` \ err ->
      (\ s -> (sep $ map text
                 [ "Printing debug message"
                 , k  ++ ":" ++show n
                 , "failed due to error:" ]) $$
              (nest 2 $ text s)) <$> prettyError err

instance MonadDebug m => MonadDebug (ExceptT e m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d

instance MonadDebug m => MonadDebug (ListT m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d

instance MonadDebug m => MonadDebug (MaybeT m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d

instance MonadDebug m => MonadDebug (ReaderT r m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d

instance MonadDebug m => MonadDebug (StateT s m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d

instance (MonadDebug m, Monoid w) => MonadDebug (WriterT w m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d

-- | Conditionally print debug string.
{-# SPECIALIZE reportS :: VerboseKey -> Int -> String -> TCM () #-}
reportS :: (HasOptions m, MonadDebug m)
        => VerboseKey -> Int -> String -> m ()
reportS k n s = verboseS k n $ displayDebugMessage n s

-- | Conditionally println debug string.
{-# SPECIALIZE reportSLn :: VerboseKey -> Int -> String -> TCM () #-}
reportSLn :: (HasOptions m, MonadDebug m)
          => VerboseKey -> Int -> String -> m ()
reportSLn k n s = verboseS k n $
  displayDebugMessage n (s ++ "\n")

-- | Conditionally render debug 'Doc' and print it.
{-# SPECIALIZE reportSDoc :: VerboseKey -> Int -> TCM Doc -> TCM () #-}
reportSDoc :: (HasOptions m, MonadDebug m)
           => VerboseKey -> Int -> TCM Doc -> m ()
reportSDoc k n d = verboseS k n $ do
  displayDebugMessage n . (++ "\n") =<< formatDebugMessage k n d

traceSLn :: (HasOptions m, MonadDebug m)
         => VerboseKey -> Int -> String -> m a -> m a
traceSLn k n s cont = ifNotM (hasVerbosity k n) cont $ {- else -} do
  traceDebugMessage n (s ++ "\n") cont

-- | Conditionally render debug 'Doc', print it, and then continue.
traceSDoc :: (HasOptions m, MonadDebug m)
          => VerboseKey -> Int -> TCM Doc -> m a -> m a
traceSDoc k n d cont = ifNotM (hasVerbosity k n) cont $ {- else -} do
  s <- formatDebugMessage k n d
  traceDebugMessage n (s ++ "\n") cont

-- | Print brackets around debug messages issued by a computation.
{-# SPECIALIZE verboseBracket :: VerboseKey -> Int -> String -> TCM a -> TCM a #-}
verboseBracket :: (HasOptions m, MonadDebug m, MonadError err m)
               => VerboseKey -> Int -> String -> m a -> m a
verboseBracket k n s m = ifNotM (hasVerbosity k n) m $ {- else -} do
  displayDebugMessage n $ "{ " ++ s ++ "\n"
  m `finally` displayDebugMessage n "}\n"
