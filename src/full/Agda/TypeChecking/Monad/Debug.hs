
module Agda.TypeChecking.Monad.Debug where

import GHC.Stack (HasCallStack, freezeCallStack, callStack)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Writer

import Data.Maybe
import Data.Monoid ( Monoid, mempty, mappend )
import Data.Semigroup ( Semigroup, (<>), Any(..) )
import Data.Traversable

import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options

import Agda.Interaction.Options
import Agda.Interaction.Response

import Agda.Utils.Except
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty
import Agda.Utils.Trie (Trie)
import qualified Agda.Utils.Trie as Trie

import Agda.Utils.Impossible

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

instance MonadDebug TCM where

  displayDebugMessage n s = liftTCM $ do
    cb <- getsTC $ stInteractionOutputCallback . stPersistentState
    cb (Resp_RunningInfo n s)

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
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapExceptT nowDebugPrinting

instance MonadDebug m => MonadDebug (ListT m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = liftListT nowDebugPrinting

instance MonadDebug m => MonadDebug (MaybeT m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapMaybeT nowDebugPrinting

instance MonadDebug m => MonadDebug (ReaderT r m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapReaderT nowDebugPrinting

instance MonadDebug m => MonadDebug (StateT s m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapStateT nowDebugPrinting

instance (MonadDebug m, Monoid w) => MonadDebug (WriterT w m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapWriterT nowDebugPrinting

-- | Conditionally print debug string.
{-# SPECIALIZE reportS :: VerboseKey -> Int -> String -> TCM () #-}
reportS :: MonadDebug m => VerboseKey -> Int -> String -> m ()
reportS k n s = verboseS k n $ displayDebugMessage n s

-- | Conditionally println debug string.
{-# SPECIALIZE reportSLn :: VerboseKey -> Int -> String -> TCM () #-}
reportSLn :: MonadDebug m => VerboseKey -> Int -> String -> m ()
reportSLn k n s = verboseS k n $
  displayDebugMessage n (s ++ "\n")

__IMPOSSIBLE_VERBOSE__ :: (HasCallStack, MonadDebug m) => String -> m a
__IMPOSSIBLE_VERBOSE__ s = do { reportSLn "impossible" 10 s ; throwImpossible err }
  where
    -- Create the "Impossible" error using *our* caller as the call site.
    err = withFileAndLine' (freezeCallStack callStack) Impossible

-- | Conditionally render debug 'Doc' and print it.
{-# SPECIALIZE reportSDoc :: VerboseKey -> Int -> TCM Doc -> TCM () #-}
reportSDoc :: MonadDebug m => VerboseKey -> Int -> TCM Doc -> m ()
reportSDoc k n d = verboseS k n $ do
  displayDebugMessage n . (++ "\n") =<< formatDebugMessage k n (locallyTC eIsDebugPrinting (const True) d)

unlessDebugPrinting :: MonadDebug m => m () -> m ()
unlessDebugPrinting = unlessM isDebugPrinting

traceSLn :: MonadDebug m => VerboseKey -> Int -> String -> m a -> m a
traceSLn k n s cont = ifNotM (hasVerbosity k n) cont $ {- else -} do
  traceDebugMessage n (s ++ "\n") cont

-- | Conditionally render debug 'Doc', print it, and then continue.
traceSDoc :: MonadDebug m => VerboseKey -> Int -> TCM Doc -> m a -> m a
traceSDoc k n d cont = ifNotM (hasVerbosity k n) cont $ {- else -} do
  s <- formatDebugMessage k n $ locallyTC eIsDebugPrinting (const True) d
  traceDebugMessage n (s ++ "\n") cont

-- | Print brackets around debug messages issued by a computation.
{-# SPECIALIZE verboseBracket :: VerboseKey -> Int -> String -> TCM a -> TCM a #-}
verboseBracket :: (MonadDebug m, MonadError err m)
               => VerboseKey -> Int -> String -> m a -> m a
verboseBracket k n s m = ifNotM (hasVerbosity k n) m $ {- else -} do
  displayDebugMessage n $ "{ " ++ s ++ "\n"
  m `finally` displayDebugMessage n "}\n"

------------------------------------------------------------------------
-- Verbosity

-- Invariant (which we may or may not currently break): Debug
-- printouts use one of the following functions:
--
--   reportS
--   reportSLn
--   reportSDoc

type VerboseKey = String

parseVerboseKey :: VerboseKey -> [String]
parseVerboseKey = wordsBy (`elem` (".:" :: String))

-- | Check whether a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
{-# SPECIALIZE hasVerbosity :: VerboseKey -> Int -> TCM Bool #-}
hasVerbosity :: MonadDebug m => VerboseKey -> Int -> m Bool
hasVerbosity k n | n < 0     = __IMPOSSIBLE__
                 | otherwise = do
    t <- getVerbosity
    let ks = parseVerboseKey k
        m  = last $ 0 : Trie.lookupPath ks t
    return (n <= m)

-- | Check whether a certain verbosity level is activated (exact match).

{-# SPECIALIZE hasExactVerbosity :: VerboseKey -> Int -> TCM Bool #-}
hasExactVerbosity :: MonadDebug m => VerboseKey -> Int -> m Bool
hasExactVerbosity k n =
  (Just n ==) . Trie.lookup (parseVerboseKey k) <$> getVerbosity

-- | Run a computation if a certain verbosity level is activated (exact match).

{-# SPECIALIZE whenExactVerbosity :: VerboseKey -> Int -> TCM () -> TCM () #-}
whenExactVerbosity :: MonadDebug m => VerboseKey -> Int -> m () -> m ()
whenExactVerbosity k n = whenM $ hasExactVerbosity k n

__CRASH_WHEN__ :: (HasCallStack, MonadTCM m, MonadDebug m) => VerboseKey -> Int -> m ()
__CRASH_WHEN__ k n = whenExactVerbosity k n (throwImpossible err)
  where
    -- Create the "Unreachable" error using *our* caller as the call site.
    err = withFileAndLine' (freezeCallStack callStack) Unreachable

-- | Run a computation if a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
{-# SPECIALIZE verboseS :: VerboseKey -> Int -> TCM () -> TCM () #-}
-- {-# SPECIALIZE verboseS :: MonadIO m => VerboseKey -> Int -> TCMT m () -> TCMT m () #-} -- RULE left-hand side too complicated to desugar
-- {-# SPECIALIZE verboseS :: MonadTCM tcm => VerboseKey -> Int -> tcm () -> tcm () #-}
verboseS :: MonadDebug m => VerboseKey -> Int -> m () -> m ()
verboseS k n action = whenM (hasVerbosity k n) $ nowDebugPrinting action

-- | Verbosity lens.
verbosity :: VerboseKey -> Lens' Int TCState
verbosity k = stPragmaOptions . verbOpt . Trie.valueAt (parseVerboseKey k) . defaultTo 0
  where
    verbOpt :: Lens' (Trie String Int) PragmaOptions
    verbOpt f opts = f (optVerbose opts) <&> \ v -> opts { optVerbose = v }

    defaultTo :: Eq a => a -> Lens' a (Maybe a)
    defaultTo x f m = f (fromMaybe x m) <&> \ v -> if v == x then Nothing else Just v
