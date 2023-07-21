
module Agda.TypeChecking.Monad.Debug
  ( module Agda.TypeChecking.Monad.Debug
  , Verbosity, VerboseKey, VerboseLevel
  ) where

import qualified Control.Exception as E
import qualified Control.DeepSeq as DeepSeq (force)

import Control.Applicative          ( liftA2 )
import Control.Monad.IO.Class       ( MonadIO(..) )
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Control  ( MonadTransControl(..), liftThrough )
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Identity
import Control.Monad.Writer

import Data.Maybe
import Data.Time                    ( getCurrentTime, getCurrentTimeZone, utcToLocalTime )
import Data.Time.Format.ISO8601.Compat ( iso8601Show )
  -- This is also exported from Data.Time.Format.ISO8601, but only from time >= 1.9

import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.Base

import Agda.Interaction.Options
import {-# SOURCE #-} Agda.Interaction.Response (Response(..))

import Agda.Utils.CallStack ( HasCallStack, withCallerCallStack )
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Syntax.Common.Pretty
import Agda.Utils.ProfileOptions
import Agda.Utils.Update
import qualified Agda.Utils.Trie as Trie

import Agda.Utils.Impossible

class (Functor m, Applicative m, Monad m) => MonadDebug m where

  formatDebugMessage :: VerboseKey -> VerboseLevel -> TCM Doc -> m String
  traceDebugMessage  :: VerboseKey -> VerboseLevel -> String -> m a -> m a

  -- | Print brackets around debug messages issued by a computation.
  verboseBracket     :: VerboseKey -> VerboseLevel -> String -> m a -> m a

  getVerbosity       :: m Verbosity
  getProfileOptions  :: m ProfileOptions

  -- | Check whether we are currently debug printing.
  isDebugPrinting    :: m Bool

  -- | Flag in a computation that we are currently debug printing.
  nowDebugPrinting   :: m a -> m a

  -- default implementation of transformed debug monad

  default formatDebugMessage
    :: (MonadTrans t, MonadDebug n, m ~ t n)
    => VerboseKey -> VerboseLevel -> TCM Doc -> m String
  formatDebugMessage k n d = lift $ formatDebugMessage k n d

  default traceDebugMessage
    :: (MonadTransControl t, MonadDebug n, m ~ t n)
    => VerboseKey -> VerboseLevel -> String -> m a -> m a
  traceDebugMessage k n s = liftThrough $ traceDebugMessage k n s

  default verboseBracket
    :: (MonadTransControl t, MonadDebug n, m ~ t n)
    => VerboseKey -> VerboseLevel -> String -> m a -> m a
  verboseBracket k n s = liftThrough $ verboseBracket k n s

  default getVerbosity
    :: (MonadTrans t, MonadDebug n, m ~ t n)
    => m Verbosity
  getVerbosity = lift getVerbosity

  default getProfileOptions
    :: (MonadTrans t, MonadDebug n, m ~ t n)
    => m ProfileOptions
  getProfileOptions = lift getProfileOptions

  default isDebugPrinting
    :: (MonadTrans t, MonadDebug n, m ~ t n)
    => m Bool
  isDebugPrinting = lift isDebugPrinting

  default nowDebugPrinting
    :: (MonadTransControl t, MonadDebug n, m ~ t n)
    => m a -> m a
  nowDebugPrinting = liftThrough nowDebugPrinting

-- Default implementations (working around the restriction to only
-- have one default signature).

defaultGetVerbosity :: HasOptions m => m Verbosity
defaultGetVerbosity = optVerbose <$> pragmaOptions

defaultGetProfileOptions :: HasOptions m => m ProfileOptions
defaultGetProfileOptions = optProfiling <$> pragmaOptions

defaultIsDebugPrinting :: MonadTCEnv m => m Bool
defaultIsDebugPrinting = asksTC envIsDebugPrinting

defaultNowDebugPrinting :: MonadTCEnv m => m a -> m a
defaultNowDebugPrinting = locallyTC eIsDebugPrinting $ const True

-- | Print a debug message if switched on.
displayDebugMessage :: MonadDebug m => VerboseKey -> VerboseLevel -> String -> m ()
displayDebugMessage k n s = traceDebugMessage k n s $ return ()

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
  -- Exception filter: Catch only the 'Impossible' exception during debug printing.
  catchMe :: Impossible -> Maybe Impossible
  catchMe = filterMaybe $ \case
    Impossible{}            -> True
    Unreachable{}           -> False
    ImpMissingDefinitions{} -> False

instance MonadDebug TCM where

  traceDebugMessage k n s cont = do
    -- Andreas, 2019-08-20, issue #4016:
    -- Force any lazy 'Impossible' exceptions to the surface and handle them.
    s  <- liftIO . catchAndPrintImpossible k n . E.evaluate . DeepSeq.force $ s
    cb <- getsTC $ stInteractionOutputCallback . stPersistentState

    -- Andreas, 2022-06-15, prefix with time stamp if `-v debug.time:100`:
    msg <- ifNotM (hasVerbosity "debug.time" 100) {-then-} (return s) {-else-} $ do
      now <- liftIO $ trailingZeros . iso8601Show <$> liftA2 utcToLocalTime getCurrentTimeZone getCurrentTime
      return $ concat [ now, ": ", s ]

    cb $ Resp_RunningInfo n msg
    cont
    where
    -- Surprisingly, iso8601Show gives us _up to_ 6 fractional digits (microseconds),
    -- but not exactly 6.  https://github.com/haskell/time/issues/211
    -- So we need to do the padding ourselves.
    -- yyyy-mm-ddThh:mm:ss.ssssss
    -- 12345678901234567890123456
    trailingZeros = take 26 . (++ repeat '0')

  formatDebugMessage k n d = catchAndPrintImpossible k n $ do
    render <$> d `catchError` \ err -> do
      renderError err <&> \ s -> vcat
        [ sep $ map text
          [ "Printing debug message"
          , k  ++ ":" ++ show n
          , "failed due to error:"
          ]
        , nest 2 $ text s
        ]

  verboseBracket k n s = applyWhenVerboseS k n $ \ m -> do
    openVerboseBracket k n s
    (m <* closeVerboseBracket k n) `catchError` \ e -> do
      closeVerboseBracketException k n
      throwError e

  getVerbosity      = defaultGetVerbosity
  getProfileOptions = defaultGetProfileOptions
  isDebugPrinting   = defaultIsDebugPrinting
  nowDebugPrinting  = defaultNowDebugPrinting

-- MonadTrans default instances

deriving instance MonadDebug m => MonadDebug (BlockT m)  -- ghc <= 8.0, GeneralizedNewtypeDeriving
instance MonadDebug m => MonadDebug (ChangeT m)
instance MonadDebug m => MonadDebug (ExceptT e m)
instance MonadDebug m => MonadDebug (MaybeT m)
instance MonadDebug m => MonadDebug (ReaderT r m)
instance MonadDebug m => MonadDebug (StateT s m)
instance (MonadDebug m, Monoid w) => MonadDebug (WriterT w m)
instance MonadDebug m => MonadDebug (IdentityT m)

-- We are lacking MonadTransControl ListT

instance MonadDebug m => MonadDebug (ListT m) where
  traceDebugMessage k n s = liftListT $ traceDebugMessage k n s
  verboseBracket    k n s = liftListT $ verboseBracket k n s
  nowDebugPrinting        = liftListT nowDebugPrinting

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
__IMPOSSIBLE_VERBOSE__ s = do
  -- Andreas, 2023-07-19, issue #6728 is fixed by manually inlining reportSLn here.
  -- reportSLn "impossible" 10 s
  -- It seems like GHC 9.6 optimization does otherwise something that throws
  -- away the debug message.
  let k = "impossible"
  let n = 10
  verboseS k n $ displayDebugMessage k n $ s ++ "\n"

  throwImpossible err
  where
    -- Create the "Impossible" error using *our* caller as the call site.
    err = withCallerCallStack Impossible

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

closeVerboseBracketException :: MonadDebug m => VerboseKey -> VerboseLevel -> m ()
closeVerboseBracketException k n = displayDebugMessage k n "} (exception)\n"


------------------------------------------------------------------------
-- Verbosity

-- Invariant (which we may or may not currently break): Debug
-- printouts use one of the following functions:
--
--   reportS
--   reportSLn
--   reportSDoc

-- | Check whether a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
{-# SPECIALIZE hasVerbosity :: VerboseKey -> VerboseLevel -> TCM Bool #-}
hasVerbosity :: MonadDebug m => VerboseKey -> VerboseLevel -> m Bool
hasVerbosity k n = do
  t <- getVerbosity
  return $ case t of
    Strict.Nothing -> n <= 1
    Strict.Just t
      -- This code is not executed if no debug flags have been given.
      | t == Trie.singleton [] 0 ->
        -- A special case for "-v0".
        n <= 0
      | otherwise ->
        let ks = parseVerboseKey k
            m  = lastWithDefault 0 $ Trie.lookupPath ks t
        in n <= m

-- | Check whether a certain verbosity level is activated (exact match).

{-# SPECIALIZE hasExactVerbosity :: VerboseKey -> VerboseLevel -> TCM Bool #-}
hasExactVerbosity :: MonadDebug m => VerboseKey -> VerboseLevel -> m Bool
hasExactVerbosity k n = do
  t <- getVerbosity
  return $ case t of
    Strict.Nothing -> n == 1
    Strict.Just t
      -- This code is not executed if no debug flags have been given.
      | t == Trie.singleton [] 0 ->
        -- A special case for "-v0".
        n == 0
      | otherwise ->
        Just n == Trie.lookup (parseVerboseKey k) t

-- | Run a computation if a certain verbosity level is activated (exact match).

{-# SPECIALIZE whenExactVerbosity :: VerboseKey -> VerboseLevel -> TCM () -> TCM () #-}
whenExactVerbosity :: MonadDebug m => VerboseKey -> VerboseLevel -> m () -> m ()
whenExactVerbosity k n = whenM $ hasExactVerbosity k n

__CRASH_WHEN__ :: (HasCallStack, MonadTCM m, MonadDebug m) => VerboseKey -> VerboseLevel -> m ()
__CRASH_WHEN__ k n = whenExactVerbosity k n (throwImpossible err)
  where
    -- Create the "Unreachable" error using *our* caller as the call site.
    err = withCallerCallStack Unreachable

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

-- | Check whether a certain profile option is activated.
{-# SPECIALIZE hasProfileOption :: ProfileOption -> TCM Bool #-}
hasProfileOption :: MonadDebug m => ProfileOption -> m Bool
hasProfileOption opt = containsProfileOption opt <$> getProfileOptions

-- | Run some code when the given profiling option is active.
whenProfile :: MonadDebug m => ProfileOption -> m () -> m ()
whenProfile opt = whenM (hasProfileOption opt)
