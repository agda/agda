{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Trace where

import Prelude hiding (null)

import Control.Monad.Reader

import {-# SOURCE #-} Agda.Interaction.Highlighting.Generate
  (highlightAsTypeChecked)

import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Options

import Agda.Utils.Function
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty (prettyShow)

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

interestingCall :: Closure Call -> Bool
interestingCall cl = case clValue cl of
    InferVar{}              -> False
    InferDef{}              -> False
    CheckArguments _ [] _ _ -> False
    SetRange{}              -> False
    NoHighlighting{}        -> False
    _                       -> True

traceCallM :: MonadTCM tcm => tcm Call -> tcm a -> tcm a
traceCallM mkCall m = flip traceCall m =<< mkCall

-- | Record a function call in the trace.
{-# SPECIALIZE traceCall :: Call -> TCM a -> TCM a #-}
traceCall :: MonadTCM tcm => Call -> tcm a -> tcm a
traceCall mkCall m = do
  let call      = mkCall
      callRange = getRange call
  -- Andreas, 2015-02-09 Make sure we do not set a range
  -- outside the current file
  verboseS "check.ranges" 10 $
    unlessNull callRange $ \ (Range is) ->
      unlessNull (mapMaybe srcFile $ map iStart is ++ map iEnd is) $ \ files -> do
        whenJustM (asks envCurrentPath) $ \ currentFile -> do
          unlessNull (filter (/= currentFile) files) $ \ wrongFiles -> do
            reportSLn "impossible" 10 $
              prettyShow call ++
              " is trying to set the current range to " ++ show callRange ++
              " which is outside of the current file " ++ show currentFile
            __IMPOSSIBLE__
  cl <- liftTCM $ buildClosure call
  let trace = local $ foldr (.) id $
        [ \e -> e { envCall = Just cl } | interestingCall cl ] ++
        [ \e -> e { envHighlightingRange = callRange }
          | callRange /= noRange && highlightCall call || isNoHighlighting call ] ++
        [ \e -> e { envRange = callRange } | callRange /= noRange ]
  wrap <- ifM (do l <- envHighlightingLevel <$> ask
                  return (l == Interactive && highlightCall call))
              (do oldRange <- envHighlightingRange <$> ask
                  return $ highlightAsTypeChecked oldRange callRange)
              (return id)
  wrap $ trace m
  where
  -- | Should the given call trigger interactive highlighting?
  highlightCall call = case call of
    CheckClause{}             -> True
    CheckPattern{}            -> True
    CheckLetBinding{}         -> True
    InferExpr{}               -> True
    CheckExprCall{}           -> True
    CheckDotPattern{}         -> True
    CheckPatternShadowing{}   -> True
    IsTypeCall{}              -> True
    IsType_{}                 -> True
    InferVar{}                -> True
    InferDef{}                -> True
    CheckArguments{}          -> True
    CheckDataDef{}            -> True
    CheckRecDef{}             -> True
    CheckConstructor{}        -> True
    CheckFunDef{}             -> True
    CheckPragma{}             -> True
    CheckPrimitive{}          -> True
    CheckIsEmpty{}            -> True
    CheckWithFunctionType{}   -> True
    CheckSectionApplication{} -> True
    ScopeCheckExpr{}          -> False
    ScopeCheckDeclaration{}   -> False
    ScopeCheckLHS{}           -> False
    NoHighlighting{}          -> True
    SetRange{}                -> False

  isNoHighlighting NoHighlighting{} = True
  isNoHighlighting _                = False

{-# SPECIALIZE traceCallCPS :: Call -> (r -> TCM a) -> ((r -> TCM a) -> TCM b) -> TCM b #-}
traceCallCPS :: MonadTCM tcm => Call -> (r -> tcm a) -> ((r -> tcm a) -> tcm b) -> tcm b
traceCallCPS mkCall ret cc = traceCall mkCall (cc ret)

{-# SPECIALIZE traceCallCPS_ :: Call -> TCM a -> (TCM a -> TCM b) -> TCM b #-}
traceCallCPS_ :: MonadTCM tcm => Call -> tcm a -> (tcm a -> tcm b) -> tcm b
traceCallCPS_ mkCall ret cc =
    traceCallCPS mkCall (const ret) (\k -> cc $ k ())

getCurrentRange :: TCM Range
getCurrentRange = asks envRange

-- | Sets the current range (for error messages etc.) to the range
--   of the given object, if it has a range (i.e., its range is not 'noRange').
setCurrentRange :: HasRange x => x -> TCM a -> TCM a
setCurrentRange x = applyUnless (null r) $ traceCall $ SetRange r
  where r = getRange x
