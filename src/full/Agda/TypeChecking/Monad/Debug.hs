
module Agda.TypeChecking.Monad.Debug
  ( module Agda.TypeChecking.Monad.Debug
  , Verbosity, VerboseKey, VerboseLevel
  ) where

import GHC.Stack (HasCallStack, freezeCallStack, callStack)

import qualified Control.Exception as E
import qualified Control.DeepSeq as DeepSeq (force)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Identity
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
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Pretty
import Agda.Utils.Update
import qualified Agda.Utils.Trie as Trie

import Agda.Utils.Impossible

class (Functor m, Applicative m, Monad m) => MonadDebug m where
  displayDebugMessage :: VerboseKey -> VerboseLevel -> String -> m ()
  displayDebugMessage k n s = traceDebugMessage k n s $ return ()

  traceDebugMessage :: VerboseKey -> VerboseLevel -> String -> m a -> m a
  traceDebugMessage k n s cont = displayDebugMessage k n s >> cont

  formatDebugMessage :: VerboseKey -> VerboseLevel -> TCM Doc -> m String

  getVerbosity :: m Verbosity

  default getVerbosity :: HasOptions m => m Verbosity
  getVerbosity = optVerbose <$> pragmaOptions

  isDebugPrinting :: m Bool

  default isDebugPrinting :: MonadTCEnv m => m Bool
  isDebugPrinting = asksTC envIsDebugPrinting

  nowDebugPrinting :: m a -> m a

  default nowDebugPrinting :: MonadTCEnv m => m a -> m a
  nowDebugPrinting = locallyTC eIsDebugPrinting $ const True

  -- | Print brackets around debug messages issued by a computation.
  verboseBracket :: VerboseKey -> VerboseLevel -> String -> m a -> m a

-- | During printing, catch internal errors of kind 'Impossible' and print them.
catchAndPrintImpossible
  :: (CatchImpossible m, Monad m)
  => VerboseKey -> VerboseLevel -> m String -> m String
catchAndPrintImpossible k n m = catchImpossibleJust catchMe m $ \ imposs -> do
  return $ render $ vcat
    [ text $ "Debug printing " ++ k ++ ":" ++ show n ++ " failed due to exception:"
    , vcat $ map (nest 2 . text) $ lines $ show imposs
    ]
  where
  -- | Exception filter: Catch only the 'Impossible' exception during debug printing.
  catchMe :: Impossible -> Maybe Impossible
  catchMe = filterMaybe $ \case
    Impossible{}            -> True
    Unreachable{}           -> False
    ImpMissingDefinitions{} -> False

instance MonadDebug TCM where

  displayDebugMessage k n s = do
    -- Andreas, 2019-08-20, issue #4016:
    -- Force any lazy 'Impossible' exceptions to the surface and handle them.
    s  <- liftIO . catchAndPrintImpossible k n . E.evaluate . DeepSeq.force $ s
    cb <- getsTC $ stInteractionOutputCallback . stPersistentState
    cb (Resp_RunningInfo n s)

  formatDebugMessage k n d = catchAndPrintImpossible k n $ do
    render <$> d `catchError` \ err -> do
      prettyError err <&> \ s -> vcat
        [ sep $ map text
          [ "Printing debug message"
          , k  ++ ":" ++ show n
          , "failed due to error:"
          ]
        , nest 2 $ text s
        ]

  verboseBracket k n s = applyWhenVerboseS k n $ \ m -> do
    openVerboseBracket k n s
    m `finally` closeVerboseBracket k n

instance MonadDebug m => MonadDebug (ExceptT e m) where
  displayDebugMessage k n s = lift $ displayDebugMessage k n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapExceptT nowDebugPrinting
  verboseBracket k n s = mapExceptT (verboseBracket k n s)

instance MonadDebug m => MonadDebug (ListT m) where
  displayDebugMessage k n s = lift $ displayDebugMessage k n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = liftListT nowDebugPrinting
  verboseBracket k n s = liftListT $ verboseBracket k n s

instance MonadDebug m => MonadDebug (MaybeT m) where
  displayDebugMessage k n s = lift $ displayDebugMessage k n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapMaybeT nowDebugPrinting
  verboseBracket k n s = MaybeT . verboseBracket k n s . runMaybeT

instance MonadDebug m => MonadDebug (ReaderT r m) where
  displayDebugMessage k n s = lift $ displayDebugMessage k n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapReaderT nowDebugPrinting
  verboseBracket k n s = mapReaderT $ verboseBracket k n s

instance MonadDebug m => MonadDebug (StateT s m) where
  displayDebugMessage k n s = lift $ displayDebugMessage k n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapStateT nowDebugPrinting
  verboseBracket k n s = mapStateT $ verboseBracket k n s

instance (MonadDebug m, Monoid w) => MonadDebug (WriterT w m) where
  displayDebugMessage k n s = lift $ displayDebugMessage k n s
  formatDebugMessage k n d = lift $ formatDebugMessage k n d
  getVerbosity = lift getVerbosity
  isDebugPrinting = lift isDebugPrinting
  nowDebugPrinting = mapWriterT nowDebugPrinting
  verboseBracket k n s = mapWriterT $ verboseBracket k n s

instance MonadDebug m => MonadDebug (ChangeT m) where
  displayDebugMessage k n s = lift $ displayDebugMessage k n s
  formatDebugMessage k n d  = lift $ formatDebugMessage k n d
  getVerbosity              = lift $ getVerbosity
  isDebugPrinting           = lift $ isDebugPrinting
  nowDebugPrinting          = mapChangeT $ nowDebugPrinting
  verboseBracket k n s      = mapChangeT $ verboseBracket k n s

instance MonadDebug m => MonadDebug (IdentityT m) where
  displayDebugMessage k n s = lift $ displayDebugMessage k n s
  formatDebugMessage k n d  = lift $ formatDebugMessage k n d
  getVerbosity              = lift $ getVerbosity
  isDebugPrinting           = lift $ isDebugPrinting
  nowDebugPrinting          = mapIdentityT $ nowDebugPrinting
  verboseBracket k n s      = mapIdentityT $ verboseBracket k n s

-- | Debug print some lines if the verbosity level for the given
--   'VerboseKey' is at least 'VerboseLevel'.
--
-- Note: In the presence of @OverloadedStrings@, just
-- @@
--   reportS key level "Literate string"
-- @@
-- gives an @Ambiguous type variable@ error in @GHC@.
-- Use the legacy functions 'reportSLn' and 'reportSDoc' instead then.
--
class ReportS a where
  reportS :: MonadDebug m => VerboseKey -> VerboseLevel -> a -> m ()

instance ReportS (TCM Doc) where reportS = reportSDoc
instance ReportS String    where reportS = reportSLn

instance ReportS [TCM Doc] where reportS k n = reportSDoc k n . fmap vcat . sequence
instance ReportS [String]  where reportS k n = reportSLn  k n . unlines
instance ReportS [Doc]     where reportS k n = reportSLn  k n . render . vcat
instance ReportS Doc       where reportS k n = reportSLn  k n . render

-- | Conditionally println debug string.
{-# SPECIALIZE reportSLn :: VerboseKey -> VerboseLevel -> String -> TCM () #-}
reportSLn :: MonadDebug m => VerboseKey -> VerboseLevel -> String -> m ()
reportSLn k n s = verboseS k n $ displayDebugMessage k n $ s ++ "\n"

__IMPOSSIBLE_VERBOSE__ :: (HasCallStack, MonadDebug m) => String -> m a
__IMPOSSIBLE_VERBOSE__ s = do { reportSLn "impossible" 10 s ; throwImpossible err }
  where
    -- Create the "Impossible" error using *our* caller as the call site.
    err = withFileAndLine' (freezeCallStack callStack) Impossible

-- | Conditionally render debug 'Doc' and print it.
{-# SPECIALIZE reportSDoc :: VerboseKey -> VerboseLevel -> TCM Doc -> TCM () #-}
reportSDoc :: MonadDebug m => VerboseKey -> VerboseLevel -> TCM Doc -> m ()
reportSDoc k n d = verboseS k n $ do
  displayDebugMessage k n . (++ "\n") =<< formatDebugMessage k n (locallyTC eIsDebugPrinting (const True) d)

-- | Debug print the result of a computation.
reportResult :: MonadDebug m => VerboseKey -> VerboseLevel -> (a -> TCM Doc) -> m a -> m a
reportResult k n debug action = do
  x <- action
  x <$ reportSDoc k n (debug x)

unlessDebugPrinting :: MonadDebug m => m () -> m ()
unlessDebugPrinting = unlessM isDebugPrinting

-- | Debug print some lines if the verbosity level for the given
--   'VerboseKey' is at least 'VerboseLevel'.
--
-- Note: In the presence of @OverloadedStrings@, just
-- @@
--   traceS key level "Literate string"
-- @@
-- gives an @Ambiguous type variable@ error in @GHC@.
-- Use the legacy functions 'traceSLn' and 'traceSDoc' instead then.
--
class TraceS a where
  traceS :: MonadDebug m => VerboseKey -> VerboseLevel -> a -> m c -> m c

instance TraceS (TCM Doc) where traceS = traceSDoc
instance TraceS String    where traceS = traceSLn

instance TraceS [TCM Doc] where traceS k n = traceSDoc k n . fmap vcat . sequence
instance TraceS [String]  where traceS k n = traceSLn  k n . unlines
instance TraceS [Doc]     where traceS k n = traceSLn  k n . render . vcat
instance TraceS Doc       where traceS k n = traceSLn  k n . render

traceSLn :: MonadDebug m => VerboseKey -> VerboseLevel -> String -> m a -> m a
traceSLn k n s = applyWhenVerboseS k n $ traceDebugMessage k n $ s ++ "\n"

-- | Conditionally render debug 'Doc', print it, and then continue.
traceSDoc :: MonadDebug m => VerboseKey -> VerboseLevel -> TCM Doc -> m a -> m a
traceSDoc k n d = applyWhenVerboseS k n $ \cont -> do
  s <- formatDebugMessage k n $ locallyTC eIsDebugPrinting (const True) d
  traceDebugMessage k n (s ++ "\n") cont

openVerboseBracket :: MonadDebug m => VerboseKey -> VerboseLevel -> String -> m ()
openVerboseBracket k n s = displayDebugMessage k n $ "{ " ++ s ++ "\n"

closeVerboseBracket :: MonadDebug m => VerboseKey -> VerboseLevel -> m ()
closeVerboseBracket k n = displayDebugMessage k n "}\n"


------------------------------------------------------------------------
-- Verbosity

-- Invariant (which we may or may not currently break): Debug
-- printouts use one of the following functions:
--
--   reportS
--   reportSLn
--   reportSDoc

parseVerboseKey :: VerboseKey -> [String]
parseVerboseKey = wordsBy (`elem` (".:" :: String))

-- | Check whether a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
{-# SPECIALIZE hasVerbosity :: VerboseKey -> VerboseLevel -> TCM Bool #-}
hasVerbosity :: MonadDebug m => VerboseKey -> VerboseLevel -> m Bool
hasVerbosity k n | n < 0     = __IMPOSSIBLE__
                 | otherwise = do
    t <- getVerbosity
    let ks = parseVerboseKey k
        m  = last $ 0 : Trie.lookupPath ks t
    return (n <= m)

-- | Check whether a certain verbosity level is activated (exact match).

{-# SPECIALIZE hasExactVerbosity :: VerboseKey -> VerboseLevel -> TCM Bool #-}
hasExactVerbosity :: MonadDebug m => VerboseKey -> VerboseLevel -> m Bool
hasExactVerbosity k n =
  (Just n ==) . Trie.lookup (parseVerboseKey k) <$> getVerbosity

-- | Run a computation if a certain verbosity level is activated (exact match).

{-# SPECIALIZE whenExactVerbosity :: VerboseKey -> VerboseLevel -> TCM () -> TCM () #-}
whenExactVerbosity :: MonadDebug m => VerboseKey -> VerboseLevel -> m () -> m ()
whenExactVerbosity k n = whenM $ hasExactVerbosity k n

__CRASH_WHEN__ :: (HasCallStack, MonadTCM m, MonadDebug m) => VerboseKey -> VerboseLevel -> m ()
__CRASH_WHEN__ k n = whenExactVerbosity k n (throwImpossible err)
  where
    -- Create the "Unreachable" error using *our* caller as the call site.
    err = withFileAndLine' (freezeCallStack callStack) Unreachable

-- | Run a computation if a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
{-# SPECIALIZE verboseS :: VerboseKey -> VerboseLevel -> TCM () -> TCM () #-}
-- {-# SPECIALIZE verboseS :: MonadIO m => VerboseKey -> VerboseLevel -> TCMT m () -> TCMT m () #-} -- RULE left-hand side too complicated to desugar
-- {-# SPECIALIZE verboseS :: MonadTCM tcm => VerboseKey -> VerboseLevel -> tcm () -> tcm () #-}
verboseS :: MonadDebug m => VerboseKey -> VerboseLevel -> m () -> m ()
verboseS k n action = whenM (hasVerbosity k n) $ nowDebugPrinting action

-- | Apply a function if a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
applyWhenVerboseS :: MonadDebug m => VerboseKey -> VerboseLevel -> (m a -> m a) -> m a -> m a
applyWhenVerboseS k n f a = ifM (hasVerbosity k n) (f a) a

-- | Verbosity lens.
verbosity :: VerboseKey -> Lens' VerboseLevel TCState
verbosity k = stPragmaOptions . verbOpt . Trie.valueAt (parseVerboseKey k) . defaultTo 0
  where
    verbOpt :: Lens' Verbosity PragmaOptions
    verbOpt f opts = f (optVerbose opts) <&> \ v -> opts { optVerbose = v }
    -- Andreas, 2019-08-20: this lens should go into Interaction.Option.Lenses!

    defaultTo :: Eq a => a -> Lens' a (Maybe a)
    defaultTo x f m = filterMaybe (== x) <$> f (fromMaybe x m)
