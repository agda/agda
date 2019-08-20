module Agda.TypeChecking.Monad.Debug where

import Agda.Interaction.Options (Verbosity, VerboseKey, VerboseLevel)
import Agda.TypeChecking.Monad.Base

import Agda.Utils.Pretty

class (Functor m, Applicative m, Monad m) => MonadDebug m where
  displayDebugMessage :: VerboseKey -> VerboseLevel -> String -> m ()
  displayDebugMessage k n s = traceDebugMessage k n s $ return ()

  traceDebugMessage :: VerboseKey -> VerboseLevel -> String -> m a -> m a
  traceDebugMessage k n s cont = displayDebugMessage k n s >> cont

  formatDebugMessage  :: VerboseKey -> VerboseLevel -> TCM Doc -> m String

  getVerbosity :: m Verbosity
  default getVerbosity :: HasOptions m => m Verbosity
  getVerbosity = optVerbose <$> pragmaOptions

  isDebugPrinting :: m Bool
  default isDebugPrinting :: MonadTCEnv m => m Bool
  isDebugPrinting = asksTC envIsDebugPrinting

  nowDebugPrinting :: m a -> m a
  default nowDebugPrinting :: MonadTCEnv m => m a -> m a
  nowDebugPrinting = locallyTC eIsDebugPrinting $ const True

  verboseBracket :: VerboseKey -> VerboseLevel -> String -> m a -> m a

instance MonadDebug TCM

reportSLn :: MonadDebug m => VerboseKey -> VerboseLevel -> String -> m ()
reportSDoc :: MonadDebug m => VerboseKey -> VerboseLevel -> TCM Doc -> m ()
