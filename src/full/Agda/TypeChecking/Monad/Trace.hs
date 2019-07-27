
module Agda.TypeChecking.Monad.Trace where

import Prelude hiding (null)

import Control.Monad.Reader

import {-# SOURCE #-} Agda.Interaction.Highlighting.Generate
  (highlightAsTypeChecked)

import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug

import Agda.Utils.Function

import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty (prettyShow)

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

interestingCall :: Call -> Bool
interestingCall = \case
    InferVar{}              -> False
    InferDef{}              -> False
    CheckArguments _ [] _ _ -> False
    SetRange{}              -> False
    NoHighlighting{}        -> False
    -- Andreas, 2019-08-07, expanded catch-all pattern.
    -- The previous presence of a catch-all raises the following question:
    -- are all of the following really interesting?
    CheckClause{}             -> True
    CheckLHS{}                -> True
    CheckPattern{}            -> True
    CheckLetBinding{}         -> True
    InferExpr{}               -> True
    CheckExprCall{}           -> True
    CheckDotPattern{}         -> True
    IsTypeCall{}              -> True
    IsType_{}                 -> True
    CheckArguments{}          -> True
    CheckMetaSolution{}       -> True
    CheckTargetType{}         -> True
    CheckDataDef{}            -> True
    CheckRecDef{}             -> True
    CheckConstructor{}        -> True
    CheckConstructorFitsIn{}  -> True
    CheckFunDefCall{}         -> True
    CheckPragma{}             -> True
    CheckPrimitive{}          -> True
    CheckIsEmpty{}            -> True
    CheckConfluence{}         -> True
    CheckWithFunctionType{}   -> True
    CheckSectionApplication{} -> True
    CheckNamedWhere{}         -> True
    ScopeCheckExpr{}          -> True
    ScopeCheckDeclaration{}   -> True
    ScopeCheckLHS{}           -> True
    CheckProjection{}         -> True
    ModuleContents{}          -> True

traceCallM :: (MonadTCM tcm, MonadDebug tcm) => tcm Call -> tcm a -> tcm a
traceCallM call m = flip traceCall m =<< call

-- | Reset 'envCall' to previous value in the continuation.
--
-- Caveat: if the last 'traceCall' did not set an 'interestingCall',
-- for example, only set the 'Range' with 'SetRange',
-- we will revert to the last interesting call.

traceCallCPS :: (MonadTCM tcm, MonadDebug tcm)
  => Call
  -> ((a -> tcm b) -> tcm b)
  -> ((a -> tcm b) -> tcm b)
traceCallCPS call k ret = do
  mcall <- asksTC envCall
  traceCall call $ k $ \ a -> do
    maybe id traceClosureCall mcall $ ret a

-- | Record a function call in the trace.

-- RULE left-hand side too complicated to desugar
-- {-# SPECIALIZE traceCall :: Call -> TCM a -> TCM a #-}
traceCall :: (MonadTCM tcm, MonadDebug tcm) => Call -> tcm a -> tcm a
traceCall call m = do
  cl <- liftTCM $ buildClosure call
  traceClosureCall cl m

traceClosureCall :: (MonadTCM tcm, MonadDebug tcm) => Closure Call -> tcm a -> tcm a
traceClosureCall cl m = do

  -- Andreas, 2016-09-13 issue #2177
  -- Since the fix of #2092 we may report an error outside the current file.
  -- (For instance, if we import a module which then happens to have the
  -- wrong name.)
  -- Thus, we no longer crash, but just report the alien range.
  -- -- Andreas, 2015-02-09 Make sure we do not set a range
  -- -- outside the current file
  verboseS "check.ranges" 90 $
    Strict.whenJust (rangeFile callRange) $ \f -> do
      currentFile <- asksTC envCurrentPath
      when (currentFile /= Just f) $ do
        reportSLn "check.ranges" 90 $
          prettyShow call ++
          " is setting the current range to " ++ show callRange ++
          " which is outside of the current file " ++ show currentFile

  -- Compute update to 'Range' and 'Call' components of 'TCEnv'.
  let withCall = localTC $ foldr (.) id $ concat $
        [ [ \e -> e { envCall = Just cl } | interestingCall call ]
        , [ \e -> e { envHighlightingRange = callRange }
          | callHasRange && highlightCall
            || isNoHighlighting
          ]
        , [ \e -> e { envRange = callRange } | callHasRange ]
        ]

  -- For interactive highlighting, also wrap computation @m@ in 'highlightAsTypeChecked':
  ifNotM (pure highlightCall `and2M` do (Interactive ==) . envHighlightingLevel <$> askTC)
    {-then-} (withCall m)
    {-else-} $ do
      oldRange <- envHighlightingRange <$> askTC
      highlightAsTypeChecked oldRange callRange $
        withCall m
  where
  call = clValue cl
  callRange = getRange call
  callHasRange = not $ null callRange

  -- | Should the given call trigger interactive highlighting?
  highlightCall = case call of
    CheckClause{}             -> True
    CheckLHS{}                -> True
    CheckPattern{}            -> True
    CheckLetBinding{}         -> True
    InferExpr{}               -> True
    CheckExprCall{}           -> True
    CheckDotPattern{}         -> True
    IsTypeCall{}              -> True
    IsType_{}                 -> True
    InferVar{}                -> True
    InferDef{}                -> True
    CheckArguments{}          -> True
    CheckMetaSolution{}       -> False
    CheckTargetType{}         -> False
    CheckDataDef{}            -> True
    CheckRecDef{}             -> True
    CheckConstructor{}        -> True
    CheckConstructorFitsIn{}  -> False
    CheckFunDefCall{}         -> True
    CheckPragma{}             -> True
    CheckPrimitive{}          -> True
    CheckIsEmpty{}            -> True
    CheckConfluence{}         -> False
    CheckWithFunctionType{}   -> True
    CheckSectionApplication{} -> True
    CheckNamedWhere{}         -> False
    ScopeCheckExpr{}          -> False
    ScopeCheckDeclaration{}   -> False
    ScopeCheckLHS{}           -> False
    NoHighlighting{}          -> True
    CheckProjection{}         -> False
    SetRange{}                -> False
    ModuleContents{}          -> False

  isNoHighlighting = case call of
    NoHighlighting{} -> True
    _ -> False

getCurrentRange :: MonadTCEnv m => m Range
getCurrentRange = asksTC envRange

-- | Sets the current range (for error messages etc.) to the range
--   of the given object, if it has a range (i.e., its range is not 'noRange').
setCurrentRange :: (MonadTCM tcm, MonadDebug tcm, HasRange x)
                => x -> tcm a -> tcm a
setCurrentRange x = applyUnless (null r) $ traceCall $ SetRange r
  where r = getRange x
