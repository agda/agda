
module Agda.TypeChecking.Monad.Debug where

import GHC.Stack (HasCallStack, freezeCallStack, callStack)

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Writer

import Data.Maybe
import Data.Monoid ( Monoid)



import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.Base

import Agda.Interaction.Options
import {-# SOURCE #-} Agda.Interaction.Response (Response(..))

import Agda.Utils.Except
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT

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

  -- | Print brackets around debug messages issued by a computation.
  verboseBracket :: VerboseKey -> Int -> String -> m a -> m a

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

  verboseBracket k n s = applyWhenVerboseS k n $ \ m -> do
    openVerboseBracket n s
    m `finally` closeVerboseBracket n

instance MonadDebug m => MonadDebug (ExceptT e m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapExceptT nowDebugPrinting
  verboseBracket k n s = applyWhenVerboseS k n $ \m -> do
    mapExceptT (verboseBracket k n s) m `catchError` \err -> do
      closeVerboseBracket n
      throwError err

instance MonadDebug m => MonadDebug (ListT m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = liftListT nowDebugPrinting
  verboseBracket k n s = liftListT $ verboseBracket k n s
    -- TODO: this may close the bracket any number of times

instance MonadDebug m => MonadDebug (MaybeT m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapMaybeT nowDebugPrinting
  verboseBracket k n s = applyWhenVerboseS k n $ \m -> MaybeT $ do
    verboseBracket k n s (runMaybeT m) >>= \case
      Just result -> return $ Just result
      Nothing     -> closeVerboseBracket n >> return Nothing

instance MonadDebug m => MonadDebug (ReaderT r m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapReaderT nowDebugPrinting
  verboseBracket k n s = mapReaderT $ verboseBracket k n s

instance MonadDebug m => MonadDebug (StateT s m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapStateT nowDebugPrinting
  verboseBracket k n s = mapStateT $ verboseBracket k n s

instance (MonadDebug m, Monoid w) => MonadDebug (WriterT w m) where
  displayDebugMessage n s = lift $ displayDebugMessage n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapWriterT nowDebugPrinting
  verboseBracket k n s = mapWriterT $ verboseBracket k n s

-- | Debug print some lines if the verbosity level for the given
--   'VerboseKey' is at least 'Int'.
--
-- Note: In the presence of @OverloadedStrings@, just
-- @@
--   reportS key level "Literate string"
-- @@
-- gives an @Ambiguous type variable@ error in @GHC@.
-- Use the legacy functions 'reportSLn' and 'reportSDoc' instead then.
--
class ReportS a where
  reportS :: MonadDebug m => VerboseKey -> Int -> a -> m ()

instance ReportS (TCM Doc) where reportS = reportSDoc
instance ReportS String    where reportS = reportSLn

instance ReportS [TCM Doc] where reportS k n = reportSDoc k n . fmap vcat . sequence
instance ReportS [String]  where reportS k n = reportSLn  k n . unlines
instance ReportS [Doc]     where reportS k n = reportSLn  k n . render . vcat
instance ReportS Doc       where reportS k n = reportSLn  k n . render

-- | Conditionally println debug string.
{-# SPECIALIZE reportSLn :: VerboseKey -> Int -> String -> TCM () #-}
reportSLn :: MonadDebug m => VerboseKey -> Int -> String -> m ()
reportSLn k n s = verboseS k n $ displayDebugMessage n $ s ++ "\n"

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

-- | Debug print some lines if the verbosity level for the given
--   'VerboseKey' is at least 'Int'.
--
-- Note: In the presence of @OverloadedStrings@, just
-- @@
--   traceS key level "Literate string"
-- @@
-- gives an @Ambiguous type variable@ error in @GHC@.
-- Use the legacy functions 'traceSLn' and 'traceSDoc' instead then.
--
class TraceS a where
  traceS :: MonadDebug m => VerboseKey -> Int -> a -> m c -> m c

instance TraceS (TCM Doc) where traceS = traceSDoc
instance TraceS String    where traceS = traceSLn

instance TraceS [TCM Doc] where traceS k n = traceSDoc k n . fmap vcat . sequence
instance TraceS [String]  where traceS k n = traceSLn  k n . unlines
instance TraceS [Doc]     where traceS k n = traceSLn  k n . render . vcat
instance TraceS Doc       where traceS k n = traceSLn  k n . render

traceSLn :: MonadDebug m => VerboseKey -> Int -> String -> m a -> m a
traceSLn k n s = applyWhenVerboseS k n $ traceDebugMessage n $ s ++ "\n"

-- | Conditionally render debug 'Doc', print it, and then continue.
traceSDoc :: MonadDebug m => VerboseKey -> Int -> TCM Doc -> m a -> m a
traceSDoc k n d = applyWhenVerboseS k n $ \cont -> do
  s <- formatDebugMessage k n $ locallyTC eIsDebugPrinting (const True) d
  traceDebugMessage n (s ++ "\n") cont

openVerboseBracket :: MonadDebug m => Int -> String -> m ()
openVerboseBracket n s = displayDebugMessage n $ "{ " ++ s ++ "\n"

closeVerboseBracket :: MonadDebug m => Int -> m ()
closeVerboseBracket n = displayDebugMessage n "}\n"


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

-- | Apply a function if a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
applyWhenVerboseS :: MonadDebug m => VerboseKey -> Int -> (m a -> m a) -> m a -> m a
applyWhenVerboseS k n f a = ifM (hasVerbosity k n) (f a) a

-- | Verbosity lens.
verbosity :: VerboseKey -> Lens' Int TCState
verbosity k = stPragmaOptions . verbOpt . Trie.valueAt (parseVerboseKey k) . defaultTo 0
  where
    verbOpt :: Lens' (Trie String Int) PragmaOptions
    verbOpt f opts = f (optVerbose opts) <&> \ v -> opts { optVerbose = v }

    defaultTo :: Eq a => a -> Lens' a (Maybe a)
    defaultTo x f m = f (fromMaybe x m) <&> \ v -> if v == x then Nothing else Just v
