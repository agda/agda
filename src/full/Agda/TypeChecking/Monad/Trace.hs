
module Agda.TypeChecking.Monad.Trace where

import Control.Monad.Reader
import Control.Monad.State

import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Monad

import {-# SOURCE #-} Agda.Interaction.Highlighting.Generate (highlightAsTypeChecked)

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

interestingCall :: Closure Call -> Bool
interestingCall cl = case clValue cl of
    InferVar _ _	      -> False
    InferDef _ _ _	      -> False
    CheckArguments _ [] _ _ _ -> False
    SetRange _ _	      -> False
    _			      -> True

-- | Record a function call in the trace.
{-# SPECIALIZE traceCall :: (Maybe r -> Call) -> TCM a -> TCM a #-}
traceCall :: MonadTCM tcm => (Maybe r -> Call) -> tcm a -> tcm a
traceCall mkCall m = do
  let call = mkCall Nothing
      r | getRange call /= noRange = const $ getRange call
        | otherwise                = id
  -- Ranges associated with the previous and current calls.
  cl <- liftTCM $ buildClosure call
  oldRange <- envRange <$> ask
  let newRange = r oldRange
  let trace | interestingCall cl = local $ \e -> e { envRange = newRange
                                                   , envCall  = Just cl }
            | otherwise          = local $ \e -> e { envRange = newRange }
  wrap <- ifM (liftM2 (&&) (envInteractiveHighlighting <$> ask)
                           (return $ highlightCall call))
            (return $ \x -> highlightAsTypeChecked x oldRange newRange)
            (return $ id)
  wrap $ trace m

  where
  -- | Tells whether on the fly highlighting should be performed for the
  -- given call.
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
    SetRange _ _                    -> False

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
