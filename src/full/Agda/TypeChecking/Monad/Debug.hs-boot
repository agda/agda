module Agda.TypeChecking.Monad.Debug where




import Agda.TypeChecking.Monad.Base


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

  verboseBracket :: VerboseKey -> Int -> String -> m a -> m a

instance MonadDebug TCM

reportSLn :: MonadDebug m => VerboseKey -> Int -> String -> m ()
reportSDoc :: MonadDebug m => VerboseKey -> Int -> TCM Doc -> m ()
