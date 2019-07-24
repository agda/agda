module Agda.TypeChecking.Warnings
  ( MonadWarning(..)
  , genericWarning
  , genericNonFatalError
  , warning_, warning, warnings
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

import qualified Data.Set as Set
import qualified Data.List as List
import Data.Maybe ( catMaybes )
import Data.Semigroup ( Semigroup, (<>) )

import Control.Monad ( forM, unless )
import Control.Monad.Reader ( ReaderT )
import Control.Monad.State ( StateT )
import Control.Monad.Trans ( lift )

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Caching
import {-# SOURCE #-} Agda.TypeChecking.Pretty
import {-# SOURCE #-} Agda.TypeChecking.Pretty.Call
import {-# SOURCE #-} Agda.TypeChecking.Pretty.Warning ()

import Agda.Syntax.Position
import Agda.Syntax.Parser

import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings

import Agda.Utils.Lens
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Except

class (MonadPretty m, MonadError TCErr m) => MonadWarning m where
  -- | Render the warning
  addWarning :: TCWarning -> m ()

instance Applicative m => Semigroup (ReaderT s m P.Doc) where
  d1 <> d2 = (<>) <$> d1 <*> d2

instance MonadWarning m => MonadWarning (ReaderT r m) where
  addWarning = lift . addWarning

instance Monad m => Semigroup (StateT s m P.Doc) where
  d1 <> d2 = (<>) <$> d1 <*> d2

instance MonadWarning m => MonadWarning (StateT s m) where
  addWarning = lift . addWarning

-- This instance is more specific than a generic instance
-- @Semigroup a => Semigroup (TCM a)@
instance {-# OVERLAPPING #-} Semigroup (TCM P.Doc) where
  d1 <> d2 = (<>) <$> d1 <*> d2

instance MonadWarning TCM where
  addWarning tcwarn = stTCWarnings `modifyTCLens` add w' tcwarn
    where
      w' = tcWarning tcwarn

      add w tcwarn tcwarns
        | onlyOnce w && elem tcwarn tcwarns = tcwarns -- Eq on TCWarning only checks head constructor
        | otherwise                         = tcwarn : tcwarns

{-# SPECIALIZE genericWarning :: P.Doc -> TCM () #-}
genericWarning :: MonadWarning m => P.Doc -> m ()
genericWarning = warning . GenericWarning

{-# SPECIALIZE genericNonFatalError :: P.Doc -> TCM () #-}
genericNonFatalError :: MonadWarning m => P.Doc -> m ()
genericNonFatalError = warning . GenericNonFatalError

{-# SPECIALIZE warning_ :: Warning -> TCM TCWarning #-}
warning_ :: MonadWarning m => Warning -> m TCWarning
warning_ w = do
  r <- viewTC eRange
  c <- viewTC eCall
  b <- areWeCaching
  -- NicifierIssues print their own error locations in their list of
  -- issues (but we might need to keep the overall range `r` for
  -- comparing ranges)
  let r' = case w of { NicifierIssue{} -> NoRange ; _ -> r }
  p <- sayWhen r' c $ prettyTCM w
  return $ TCWarning r w p b

-- UNUSED Liang-Ting Chen 2019-07-16
---- | @applyWarningMode@ filters out the warnings the user has not requested
---- Users are not allowed to ignore non-fatal errors.
--
--applyWarningMode :: WarningMode -> Warning -> Maybe Warning
--applyWarningMode wm w = case classifyWarning w of
--  ErrorWarnings -> Just w
--  AllWarnings   -> w <$ guard (Set.member (warningName w) $ wm ^. warningSet)

{-# SPECIALIZE warnings :: [Warning] -> TCM () #-}
warnings :: MonadWarning m => [Warning] -> m ()
warnings ws = do

  wmode <- optWarningMode <$> pragmaOptions

  -- We collect *all* of the warnings no matter whether they are in the @warningSet@
  -- or not. If we find one which should be turned into an error, we keep processing
  -- the rest of the warnings and *then* report all of the errors at once.
  merrs <- forM ws $ \ w' -> do
    tcwarn <- warning_ w'
    if wmode ^. warn2Error && warningName w' `elem` wmode ^. warningSet
    then pure (Just tcwarn)
    else Nothing <$ addWarning tcwarn

  let errs = catMaybes merrs
  unless (null errs) $ typeError $ NonFatalErrors errs

{-# SPECIALIZE warning :: Warning -> TCM () #-}
warning :: MonadWarning m => Warning -> m ()
warning = warnings . pure

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


-- | running the Parse monad

runPM :: PM a -> TCM a
runPM m = do
  (res, ws) <- runPMIO m
  mapM_ (warning . ParseWarning) ws
  case res of
    Left  e -> throwError (Exception (getRange e) (P.pretty e))
    Right a -> return a
