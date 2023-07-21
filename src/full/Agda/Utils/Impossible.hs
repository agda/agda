{-# OPTIONS_GHC -Wunused-imports #-}

------------------------------------------------------------------------
-- | An interface for reporting \"impossible\" errors
------------------------------------------------------------------------


module Agda.Utils.Impossible where

import Control.Exception (Exception(..), throw, catchJust)
import Control.DeepSeq
import Agda.Utils.CallStack.Base
    ( CallStack
    , HasCallStack
    , prettyCallStack
    , withCallerCallStack
    )

-- | \"Impossible\" errors, annotated with a file name and a line
-- number corresponding to the source code location of the error.

data Impossible

  = Impossible CallStack
    -- ^ We reached a program point which should be unreachable.

  | Unreachable CallStack
    -- ^ @Impossible@ with a different error message.
    --   Used when we reach a program point which can in principle
    --   be reached, but not for a certain run.

  | ImpMissingDefinitions [String] String
    -- ^ We reached a program point without all the required
    -- primitives or BUILTIN to proceed forward.
    -- @ImpMissingDefinitions neededDefs forThis@

-- Identify all values of Impossible. We use Impossible as a stand-in for the empty type, so all
-- values are morally equal.
instance Eq Impossible where
  _ == _ = True

instance Ord Impossible where
  compare _ _ = EQ

instance NFData Impossible where
  rnf _ = ()

instance Show Impossible where
  show (Impossible loc) = unlines
    [ "An internal error has occurred. Please report this as a bug."
    , "Location of the error: " ++ prettyCallStack loc
    ]
  show (Unreachable loc) = unlines
    [ "We reached a program point we did not want to reach."
    , "Location of the error: " ++ prettyCallStack loc
    ]
  show (ImpMissingDefinitions needed forthis) = unlines
    [ "The following builtins or primitives need to be bound to use " ++ forthis ++ ":"
    , unwords needed
    ]

instance Exception Impossible

-- | Abort by throwing an \"impossible\" error. You should not use
-- this function directly. Instead use __IMPOSSIBLE__

throwImpossible :: Impossible -> a
throwImpossible = throw

-- | Monads in which we can catch an \"impossible\" error, if possible.

class CatchImpossible m where

  -- | Catch any 'Impossible' exception.
  catchImpossible :: m a -> (Impossible -> m a) -> m a
  catchImpossible = catchImpossibleJust Just

  -- | Catch only 'Impossible' exceptions selected by the filter.
  catchImpossibleJust :: (Impossible -> Maybe b) -> m a -> (b -> m a) -> m a
  catchImpossibleJust = flip . handleImpossibleJust

  -- | Version of 'catchImpossible' with argument order suiting short handlers.
  handleImpossible :: (Impossible -> m a) -> m a -> m a
  handleImpossible = flip catchImpossible

  -- | Version of 'catchImpossibleJust' with argument order suiting short handlers.
  handleImpossibleJust :: (Impossible -> Maybe b) -> (b -> m a) -> m a -> m a
  handleImpossibleJust = flip . catchImpossibleJust

  {-# MINIMAL catchImpossibleJust | handleImpossibleJust #-}

instance CatchImpossible IO where
  catchImpossibleJust = catchJust

-- | Throw an "Impossible" error reporting the *caller's* call site.

__IMPOSSIBLE__ :: HasCallStack => a
__IMPOSSIBLE__ = withCallerCallStack $ throwImpossible . Impossible

impossible :: HasCallStack => Impossible
impossible = withCallerCallStack Impossible

-- | Throw an "Unreachable" error reporting the *caller's* call site.
-- Note that this call to "withFileAndLine" will be filtered out
-- due its filter on the srcLocModule.

__UNREACHABLE__ :: HasCallStack => a
__UNREACHABLE__ = withCallerCallStack $ throwImpossible . Unreachable
