
module Agda.TypeChecking.Monad.Trace where

import Control.Monad.Reader
import Control.Monad.State

import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Monad

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
  cl <- liftTCM $ buildClosure call
  let trace | interestingCall cl = local $ \e -> e { envRange = r (envRange e)
                                                   , envCall  = Just cl }
            | otherwise          = local $ \e -> e { envRange = r (envRange e) }
  trace m

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
