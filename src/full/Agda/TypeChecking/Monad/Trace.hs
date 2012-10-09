
module Agda.TypeChecking.Monad.Trace where

import Control.Monad.Reader
import Control.Monad.State

import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Monad

import {-# SOURCE #-} Agda.Interaction.Highlighting.Generate
  (highlightAsTypeChecked)

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

interestingCall :: Closure Call -> Bool
interestingCall cl = case clValue cl of
    InferVar _ _	      -> False
    InferDef _ _ _	      -> False
    CheckArguments _ [] _ _ _ -> False
    SetRange _ _	      -> False
    NoHighlighting {}         -> False
    _			      -> True

traceCallM :: MonadTCM tcm => tcm (Maybe r -> Call) -> tcm a -> tcm a
traceCallM mkCall m = flip traceCall m =<< mkCall

-- | Record a function call in the trace.
{-# SPECIALIZE traceCall :: (Maybe r -> Call) -> TCM a -> TCM a #-}
traceCall :: MonadTCM tcm => (Maybe r -> Call) -> tcm a -> tcm a
traceCall mkCall m = do
  let call      = mkCall Nothing
      callRange = getRange call
  cl <- liftTCM $ buildClosure call
  let trace = local $
        (if interestingCall cl then
           \e -> e { envCall = Just cl }
         else
           id) .
        (if callRange /= noRange || isNoHighlighting call then
           \e -> e { envHighlightingRange = callRange
                   }
         else
           id) .
        (if callRange /= noRange then
           \e -> e { envRange = callRange
                   }
         else
           id)
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
    CheckExpr _ _ _                 -> True
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
getCurrentRange = envRange <$> ask

setCurrentRange :: Range -> TCM a -> TCM a
setCurrentRange r
  | r == noRange = id
  | otherwise    = traceCall (SetRange r)
