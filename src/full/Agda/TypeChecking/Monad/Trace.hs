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
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

interestingCall :: Closure Call -> Bool
interestingCall cl = case clValue cl of
    InferVar _ _              -> False
    InferDef _ _ _            -> False
    CheckArguments _ [] _ _ _ -> False
    SetRange _ _              -> False
    NoHighlighting {}         -> False
    _                         -> True

traceCallM :: MonadTCM tcm => tcm (Maybe r -> Call) -> tcm a -> tcm a
traceCallM mkCall m = flip traceCall m =<< mkCall

-- | Record a function call in the trace.
{-# SPECIALIZE traceCall :: (Maybe r -> Call) -> TCM a -> TCM a #-}
traceCall :: MonadTCM tcm => (Maybe r -> Call) -> tcm a -> tcm a
traceCall mkCall m = do
  let call      = mkCall Nothing
      callRange = getRange call
  -- Andreas, 2015-02-09 Make sure we do not set a range
  -- outside the current file
  unlessNull callRange $ \ (Range is) ->
    unlessNull (mapMaybe srcFile $ map iStart is ++ map iEnd is) $ \ files -> do
      whenJustM (asks envCurrentPath) $ \ currentFile -> do
        unlessNull (filter (/= currentFile) files) $ \ wrongFiles -> do
          reportSLn "impossible" 10 $
            "Someone is trying to set the current range to " ++ show callRange ++
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
    CheckClause _ _ _               -> True
    CheckPattern _ _ _ _            -> True
    CheckLetBinding _ _             -> True
    InferExpr _ _                   -> True
    CheckExprCall _ _ _             -> True
    CheckDotPattern _ _ _           -> True
    CheckPatternShadowing _ _       -> True
    IsTypeCall _ _ _                -> True
    IsType_ _ _                     -> True
    InferVar _ _                    -> True
    InferDef _ _ _                  -> True
    CheckArguments _ _ _ _ _        -> True
    CheckDataDef _ _ _ _ _          -> True
    CheckRecDef _ _ _ _ _           -> True
    CheckConstructor _ _ _ _ _      -> True
    CheckFunDef _ _ _ _             -> True
    CheckPragma _ _ _               -> True
    CheckPrimitive _ _ _ _          -> True
    CheckIsEmpty _ _ _              -> True
    CheckWithFunctionType _ _       -> True
    CheckSectionApplication _ _ _ _ -> True
    ScopeCheckExpr _ _              -> False
    ScopeCheckDeclaration _ _       -> False
    ScopeCheckLHS _ _ _             -> False
    NoHighlighting _                -> True
    SetRange _ _                    -> False

  isNoHighlighting (NoHighlighting {}) = True
  isNoHighlighting _                   = False

{-# SPECIALIZE traceCall_ :: (Maybe () -> Call) -> TCM r -> TCM r #-}
traceCall_ :: MonadTCM tcm => (Maybe () -> Call) -> tcm r -> tcm r
traceCall_ mkCall = traceCall (mkCall . fmap (const ()))

{-# SPECIALIZE traceCallCPS :: (Maybe r -> Call) -> (r -> TCM a) -> ((r -> TCM a) -> TCM b) -> TCM b #-}
traceCallCPS :: MonadTCM tcm => (Maybe r -> Call) -> (r -> tcm a) -> ((r -> tcm a) -> tcm b) -> tcm b
traceCallCPS mkCall ret cc = traceCall mkCall (cc ret)

{-# SPECIALIZE traceCallCPS_ :: (Maybe () -> Call) -> TCM a -> (TCM a -> TCM b) -> TCM b #-}
traceCallCPS_ :: MonadTCM tcm => (Maybe () -> Call) -> tcm a -> (tcm a -> tcm b) -> tcm b
traceCallCPS_ mkCall ret cc =
    traceCallCPS mkCall (const ret) (\k -> cc $ k ())

getCurrentRange :: TCM Range
getCurrentRange = asks envRange

-- | Sets the current range (for error messages etc.) to the range
--   of the given object, if it has a range (i.e., its range is not 'noRange').
setCurrentRange :: HasRange x => x -> TCM a -> TCM a
setCurrentRange x = applyUnless (null r) $ traceCall $ SetRange r
  where r = getRange x
