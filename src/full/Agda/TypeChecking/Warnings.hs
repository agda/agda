{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Warnings where

import qualified Data.List as List

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Errors
import {-# SOURCE #-} Agda.TypeChecking.Pretty

import Agda.Syntax.Position
import Agda.Syntax.Parser

import Agda.Interaction.Options

import Agda.Utils.Lens
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Except

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ((<$>))
#endif



{-# SPECIALIZE genericWarning :: P.Doc -> TCM () #-}
genericWarning :: MonadTCM tcm => P.Doc -> tcm ()
genericWarning = warning . GenericWarning

{-# SPECIALIZE genericNonFatalError :: P.Doc -> TCM () #-}
genericNonFatalError :: MonadTCM tcm => P.Doc -> tcm ()
genericNonFatalError = warning . GenericNonFatalError

{-# SPECIALIZE warning_ :: Warning -> TCM TCWarning #-}
warning_ :: MonadTCM tcm => Warning -> tcm TCWarning
warning_ w = do
  r <- view eRange
  c <- view eCall
  -- NicifierIssues print their own error locations in their list of
  -- issues (but we might need to keep the overall range `r` for
  -- comparing ranges)
  let r' = case w of { NicifierIssue{} -> NoRange ; _ -> r }
  p <- liftTCM $ sayWhen r' c $ prettyWarning w
  liftTCM $ return $ TCWarning r w p

{-# SPECIALIZE warning :: Warning -> TCM () #-}
warning :: MonadTCM tcm => Warning -> tcm ()
warning w = do
  tcwarn <- warning_ w
  wmode <- optWarningMode <$> pragmaOptions
  case wmode of
    IgnoreAllWarnings -> case classifyWarning w of
                           -- not allowed to ignore non-fatal errors
                           ErrorWarnings -> raiseWarning tcwarn
                           AllWarnings -> return ()
    TurnIntoErrors -> typeError $ NonFatalErrors [tcwarn]
    LeaveAlone -> raiseWarning tcwarn
  where raiseWarning tcw = stTCWarnings %= (tcw :)

-- | Classifying warnings: some are benign, others are (non-fatal) errors

data WhichWarnings =
    ErrorWarnings -- ^ warnings that will be turned into errors
  | AllWarnings   -- ^ all warnings, including errors and benign ones
  -- Note: order of constructors is important for the derived Ord instance
  deriving (Eq, Ord)

isUnsolvedWarning :: Warning -> Bool
isUnsolvedWarning w = case w of
  UnsolvedMetaVariables{}    -> True
  UnsolvedInteractionMetas{} -> True
  UnsolvedConstraints{}      -> True
 -- rest
  _                          -> False

classifyWarning :: Warning -> WhichWarnings
classifyWarning w = case w of
  OldBuiltin{}               -> AllWarnings
  EmptyRewritePragma         -> AllWarnings
  UselessPublic              -> AllWarnings
  UnreachableClauses{}       -> AllWarnings
  UselessInline{}            -> AllWarnings
  GenericWarning{}           -> AllWarnings
  DeprecationWarning{}       -> AllWarnings
  NicifierIssue{}            -> AllWarnings
  TerminationIssue{}         -> ErrorWarnings
  CoverageIssue{}            -> ErrorWarnings
  CoverageNoExactSplit{}     -> ErrorWarnings
  NotStrictlyPositive{}      -> ErrorWarnings
  UnsolvedMetaVariables{}    -> ErrorWarnings
  UnsolvedInteractionMetas{} -> ErrorWarnings
  UnsolvedConstraints{}      -> ErrorWarnings
  GenericNonFatalError{}     -> ErrorWarnings
  SafeFlagPostulate{}        -> ErrorWarnings
  SafeFlagPragma{}           -> ErrorWarnings
  SafeFlagNonTerminating     -> ErrorWarnings
  SafeFlagTerminating        -> ErrorWarnings
  SafeFlagPrimTrustMe        -> ErrorWarnings
  SafeFlagNoPositivityCheck  -> ErrorWarnings
  SafeFlagPolarity           -> ErrorWarnings
  ParseWarning{}             -> ErrorWarnings

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
