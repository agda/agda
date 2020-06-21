{-# LANGUAGE TypeFamilies #-} -- for type equality ~

module Agda.TypeChecking.Warnings
  ( MonadWarning(..)
  , genericWarning
  , genericNonFatalError
  , warning'_, warning_, warning', warning, warnings
  , raiseWarningsOnUsage
  , isUnsolvedWarning
  , isMetaWarning
  , isMetaTCWarning
  , onlyShowIfUnsolved
  , WhichWarnings(..), classifyWarning
  -- not exporting constructor of WarningsAndNonFatalErrors
  , WarningsAndNonFatalErrors, tcWarnings, nonFatalErrors
  , emptyWarningsAndNonFatalErrors, classifyWarnings
  , runPM
  ) where

import GHC.Stack ( HasCallStack, callStack, freezeCallStack )

import Control.Monad ( forM, unless )
import Control.Monad.Except
import Control.Monad.Reader ( ReaderT )
import Control.Monad.State ( StateT )
import Control.Monad.Trans ( lift )

import qualified Data.List as List
import qualified Data.Map  as Map
import qualified Data.Set  as Set
import Data.Maybe     ( catMaybes )
import Data.Semigroup ( Semigroup, (<>) )

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Caching
import {-# SOURCE #-} Agda.TypeChecking.Pretty (MonadPretty, prettyTCM)
import {-# SOURCE #-} Agda.TypeChecking.Pretty.Call
import {-# SOURCE #-} Agda.TypeChecking.Pretty.Warning ( prettyWarning )

import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Parser

import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings
import {-# SOURCE #-} Agda.Interaction.Highlighting.Generate (highlightWarning)

import Agda.Utils.Lens
import qualified Agda.Utils.Pretty as P

import Agda.Utils.Impossible


-- * The warning monad
---------------------------------------------------------------------------

class (MonadPretty m, MonadError TCErr m) => MonadWarning m where
  -- | Store a warning and generate highlighting from it.
  addWarning :: TCWarning -> m ()

  default addWarning
    :: (MonadWarning n, MonadTrans t, t n ~ m)
    => TCWarning -> m ()
  addWarning = lift . addWarning

instance MonadWarning m => MonadWarning (ReaderT r m)
instance MonadWarning m => MonadWarning (StateT s m)

instance MonadWarning TCM where
  addWarning tcwarn = do
    stTCWarnings `modifyTCLens` add w' tcwarn
    highlightWarning tcwarn
    where
      w' = tcWarning tcwarn

      add w tcwarn tcwarns
        | onlyOnce w && elem tcwarn tcwarns = tcwarns -- Eq on TCWarning only checks head constructor
        | otherwise                         = tcwarn : tcwarns

-- * Raising warnings
---------------------------------------------------------------------------

{-# SPECIALIZE genericWarning :: P.Doc -> TCM () #-}
genericWarning :: MonadWarning m => P.Doc -> m ()
genericWarning = warning . GenericWarning

{-# SPECIALIZE genericNonFatalError :: P.Doc -> TCM () #-}
genericNonFatalError :: MonadWarning m => P.Doc -> m ()
genericNonFatalError = warning . GenericNonFatalError

{-# SPECIALIZE warning'_ :: AgdaSourceErrorLocation -> Warning -> TCM TCWarning #-}
warning'_ :: (MonadWarning m) => AgdaSourceErrorLocation -> Warning -> m TCWarning
warning'_ fl w = do
  r <- viewTC eRange
  c <- viewTC eCall
  b <- areWeCaching
  -- NicifierIssues print their own error locations in their list of
  -- issues (but we might need to keep the overall range `r` for
  -- comparing ranges)
  let r' = case w of { NicifierIssue{} -> NoRange ; _ -> r }
  p <- sayWhen r' c $ prettyWarning w
  return $ TCWarning fl r w p b

{-# SPECIALIZE warning_ :: Warning -> TCM TCWarning #-}
warning_ :: (HasCallStack, MonadWarning m) => Warning -> m TCWarning
warning_ w = withFileAndLine $ \ file line ->
  warning'_ (AgdaSourceErrorLocation file line) w

-- UNUSED Liang-Ting Chen 2019-07-16
---- | @applyWarningMode@ filters out the warnings the user has not requested
---- Users are not allowed to ignore non-fatal errors.
--
--applyWarningMode :: WarningMode -> Warning -> Maybe Warning
--applyWarningMode wm w = case classifyWarning w of
--  ErrorWarnings -> Just w
--  AllWarnings   -> w <$ guard (Set.member (warningName w) $ wm ^. warningSet)

{-# SPECIALIZE warnings' :: AgdaSourceErrorLocation -> [Warning] -> TCM () #-}
warnings' :: MonadWarning m => AgdaSourceErrorLocation -> [Warning] -> m ()
warnings' fl ws = do

  wmode <- optWarningMode <$> pragmaOptions

  -- We collect *all* of the warnings no matter whether they are in the @warningSet@
  -- or not. If we find one which should be turned into an error, we keep processing
  -- the rest of the warnings and *then* report all of the errors at once.
  merrs <- forM ws $ \ w' -> do
    tcwarn <- warning'_ fl w'
    if wmode ^. warn2Error && warningName w' `elem` wmode ^. warningSet
    then pure (Just tcwarn)
    else Nothing <$ addWarning tcwarn

  let errs = catMaybes merrs
  unless (null errs) $ typeError' fl $ NonFatalErrors errs

{-# SPECIALIZE warnings :: HasCallStack => [Warning] -> TCM () #-}
warnings :: (HasCallStack, MonadWarning m) => [Warning] -> m ()
warnings ws = withFileAndLine' (freezeCallStack callStack) $ \ file line ->
  warnings' (AgdaSourceErrorLocation file line) ws

{-# SPECIALIZE warning' :: AgdaSourceErrorLocation -> Warning -> TCM () #-}
warning' :: MonadWarning m => AgdaSourceErrorLocation -> Warning -> m ()
warning' fl = warnings' fl . pure

{-# SPECIALIZE warning :: HasCallStack => Warning -> TCM () #-}
warning :: (HasCallStack, MonadWarning m) => Warning -> m ()
warning w = withFileAndLine' (freezeCallStack callStack)  $ \ file line ->
  warning' (AgdaSourceErrorLocation file line) w

-- | Raise every 'WARNING_ON_USAGE' connected to a name.
{-# SPECIALIZE raiseWarningsOnUsage :: QName -> TCM () #-}
raiseWarningsOnUsage :: (MonadWarning m, ReadTCState m) => QName -> m ()
raiseWarningsOnUsage d = do
  -- In case we find a defined name, we start by checking whether there's
  -- a warning attached to it
  reportSLn "scope.warning.usage" 50 $ "Checking usage of " ++ P.prettyShow d
  mapM_ (warning . UserWarning) =<< Map.lookup d <$> getUserWarnings


-- * Classifying warnings
---------------------------------------------------------------------------

isUnsolvedWarning :: Warning -> Bool
isUnsolvedWarning w = warningName w `Set.member` unsolvedWarnings

isMetaWarning :: Warning -> Bool
isMetaWarning w = case w of
   UnsolvedInteractionMetas{} -> True
   UnsolvedMetaVariables{}    -> True
   _                          -> False

isMetaTCWarning :: TCWarning -> Bool
isMetaTCWarning = isMetaWarning . tcWarning

-- | Should we only emit a single warning with this constructor.
onlyOnce :: Warning -> Bool
onlyOnce InversionDepthReached{} = True
onlyOnce _ = False

onlyShowIfUnsolved :: Warning -> Bool
onlyShowIfUnsolved InversionDepthReached{} = True
onlyShowIfUnsolved _ = False

-- | Classifying warnings: some are benign, others are (non-fatal) errors

data WhichWarnings =
    ErrorWarnings -- ^ warnings that will be turned into errors
  | AllWarnings   -- ^ all warnings, including errors and benign ones
  -- Note: order of constructors is important for the derived Ord instance
  deriving (Eq, Ord)

classifyWarning :: Warning -> WhichWarnings
classifyWarning w =
  if warningName w `Set.member` errorWarnings
  then ErrorWarnings
  else AllWarnings

-- | Assorted warnings and errors to be displayed to the user
data WarningsAndNonFatalErrors = WarningsAndNonFatalErrors
  { tcWarnings     :: [TCWarning]
  , nonFatalErrors :: [TCWarning]
  }

-- | The only way to construct a empty WarningsAndNonFatalErrors

emptyWarningsAndNonFatalErrors :: WarningsAndNonFatalErrors
emptyWarningsAndNonFatalErrors = WarningsAndNonFatalErrors [] []

classifyWarnings :: [TCWarning] -> WarningsAndNonFatalErrors
classifyWarnings ws = WarningsAndNonFatalErrors warnings errors
  where
    partite = (< AllWarnings) . classifyWarning . tcWarning
    (errors, warnings) = List.partition partite ws


-- * Warnings in the parser
---------------------------------------------------------------------------

-- | running the Parse monad

runPM :: PM a -> TCM a
runPM m = do
  (res, ws) <- runPMIO m
  mapM_ (warning . ParseWarning) ws
  case res of
    Left  e -> throwError (Exception (getRange e) (P.pretty e))
    Right a -> return a
