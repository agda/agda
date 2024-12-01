module Agda.Interaction.Command
  ( CommandM, localStateCommandM, liftLocalState, revLift, revLiftTC
  ) where

import Control.Monad.State ( MonadState(..), execStateT, lift )

import Agda.TypeChecking.Monad.Base ( TCM,MonadTCState, TCState, getTC, putTC )
import Agda.TypeChecking.Monad.State ( localTCState )

import Agda.Interaction.Base ( CommandM' )

------------------------------------------------------------------------
-- The CommandM monad

type CommandM  = CommandM' TCM

-- | Restore both 'TCState' and 'CommandState'.

localStateCommandM :: CommandM a -> CommandM a
localStateCommandM m = do
  cSt <- get
  tcSt <- getTC
  x <- m
  putTC tcSt
  put cSt
  return x

-- | Restore 'TCState', do not touch 'CommandState'.

liftLocalState :: TCM a -> CommandM a
liftLocalState = lift . localTCState

-- | Build an opposite action to 'lift' for state monads.

revLift
    :: MonadState st m
    => (forall c . m c -> st -> k (c, st))      -- ^ run
    -> (forall b . k b -> m b)                  -- ^ lift
    -> (forall x . (m a -> k x) -> k x) -> m a  -- ^ reverse lift in double negative position
revLift run lift' f = do
    st <- get
    (a, st') <- lift' $ f (`run` st)
    put st'
    return a

revLiftTC
    :: MonadTCState m
    => (forall c . m c -> TCState -> k (c, TCState))  -- ^ run
    -> (forall b . k b -> m b)                        -- ^ lift
    -> (forall x . (m a -> k x) -> k x) -> m a        -- ^ reverse lift in double negative position
revLiftTC run lift' f = do
    st <- getTC
    (a, st') <- lift' $ f (`run` st)
    putTC st'
    return a
