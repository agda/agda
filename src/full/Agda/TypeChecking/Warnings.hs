{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Warnings where

import qualified Data.Set as Set
import qualified Data.List as List
import Data.Maybe ( catMaybes )
import Control.Monad ( guard, forM, unless )

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Caching
import {-# SOURCE #-} Agda.TypeChecking.Errors
import {-# SOURCE #-} Agda.TypeChecking.Pretty

import Agda.Syntax.Position
import Agda.Syntax.Parser
import Agda.Syntax.Concrete.Definitions (DeclarationWarning(..))

import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings

import Agda.Utils.Lens
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Except

{-# SPECIALIZE genericWarning :: P.Doc -> TCM () #-}
genericWarning :: MonadTCM tcm => P.Doc -> tcm ()
genericWarning = warning . GenericWarning

{-# SPECIALIZE genericNonFatalError :: P.Doc -> TCM () #-}
genericNonFatalError :: MonadTCM tcm => P.Doc -> tcm ()
genericNonFatalError = warning . GenericNonFatalError

{-# SPECIALIZE warning_ :: Warning -> TCM TCWarning #-}
warning_ :: MonadTCM tcm => Warning -> tcm TCWarning
warning_ w = do
  r <- viewTC eRange
  c <- viewTC eCall
  b <- liftTCM areWeCaching
  -- NicifierIssues print their own error locations in their list of
  -- issues (but we might need to keep the overall range `r` for
  -- comparing ranges)
  let r' = case w of { NicifierIssue{} -> NoRange ; _ -> r }
  p <- liftTCM $ sayWhen r' c $ prettyWarning w
  liftTCM $ return $ TCWarning r w p b

-- | @applyWarningMode@ filters out the warnings the user has not requested
-- Users are not allowed to ignore non-fatal errors.

applyWarningMode :: WarningMode -> Warning -> Maybe Warning
applyWarningMode wm w = case classifyWarning w of
  ErrorWarnings -> Just w
  AllWarnings   -> w <$ guard (Set.member (warningName w) $ wm ^. warningSet)

{-# SPECIALIZE warnings :: [Warning] -> TCM () #-}
warnings :: MonadTCM tcm => [Warning] -> tcm ()
warnings ws = do

  wmode <- optWarningMode <$> pragmaOptions

  let add w tcwarn tcwarns
        | onlyOnce w && elem tcwarn tcwarns = tcwarns -- Eq on TCWarning only checks head constructor
        | otherwise                         = tcwarn : tcwarns

  -- We collect *all* of the warnings no matter whether they are in the @warningSet@
  -- or not. If we find one which should be turned into an error, we keep processing
  -- the rest of the warnings and *then* report all of the errors at once.
  merrs <- forM ws $ \ w' -> do
    tcwarn <- warning_ w'
    if wmode ^. warn2Error && warningName w' `elem` wmode ^. warningSet
    then pure (Just tcwarn)
    else Nothing <$ (stTCWarnings `modifyTCLens` add w' tcwarn)

  let errs = catMaybes merrs
  unless (null errs) $ typeError $ NonFatalErrors errs

{-# SPECIALIZE warning :: Warning -> TCM () #-}
warning :: MonadTCM tcm => Warning -> tcm ()
warning = warnings . pure


-- | Classifying warnings: some are benign, others are (non-fatal) errors

data WhichWarnings =
    ErrorWarnings -- ^ warnings that will be turned into errors
  | AllWarnings   -- ^ all warnings, including errors and benign ones
  -- Note: order of constructors is important for the derived Ord instance
  deriving (Eq, Ord)

isUnsolvedWarning :: Warning -> Bool
isUnsolvedWarning w = warningName w `elem` unsolvedWarnings

classifyWarning :: Warning -> WhichWarnings
classifyWarning w =
  if warningName w `elem` errorWarnings
  then ErrorWarnings
  else AllWarnings

-- | Should we only emit a single warning with this constructor.
onlyOnce :: Warning -> Bool
onlyOnce InversionDepthReached{} = True
onlyOnce _ = False

onlyShowIfUnsolved :: Warning -> Bool
onlyShowIfUnsolved InversionDepthReached{} = True
onlyShowIfUnsolved _ = False

classifyWarnings :: [TCWarning] -> ([TCWarning], [TCWarning])
classifyWarnings = List.partition $ (< AllWarnings) . classifyWarning . tcWarning

-- | running the Parse monad

runPM :: PM a -> TCM a
runPM m = do
  (res, ws) <- runPMIO m
  mapM_ (warning . ParseWarning) ws
  case res of
    Left  e -> throwError (Exception (getRange e) (P.pretty e))
    Right a -> return a
