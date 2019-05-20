module Agda.TypeChecking.Monad.Debug where

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options

import Agda.Utils.Pretty
import Agda.Utils.Trie (Trie)

type VerboseKey = String

class (Functor m, Applicative m, Monad m) => MonadDebug m where
  displayDebugMessage :: Int -> String -> m ()
  displayDebugMessage n s = traceDebugMessage n s $ return ()

  traceDebugMessage :: Int -> String -> m a -> m a
  traceDebugMessage n s cont = displayDebugMessage n s >> cont

  formatDebugMessage  :: VerboseKey -> Int -> TCM Doc -> m String

  getVerbosity :: m (Trie String Int)
  default getVerbosity :: HasOptions m => m (Trie String Int)
  getVerbosity = optVerbose <$> pragmaOptions

  isDebugPrinting :: m Bool
  default isDebugPrinting :: MonadTCEnv m => m Bool
  isDebugPrinting = asksTC envIsDebugPrinting

  nowDebugPrinting :: m a -> m a
  default nowDebugPrinting :: MonadTCEnv m => m a -> m a
  nowDebugPrinting = locallyTC eIsDebugPrinting $ const True

instance (MonadIO m) => MonadDebug (TCMT m)

reportS :: (HasOptions m, MonadDebug m)
        => VerboseKey -> Int -> String -> m ()
reportSLn :: (HasOptions m, MonadDebug m)
          => VerboseKey -> Int -> String -> m ()
reportSDoc :: (HasOptions m, MonadDebug m)
           => VerboseKey -> Int -> TCM Doc -> m ()

