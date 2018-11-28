------------------------------------------------------------------------
-- | An interface for reporting \"impossible\" errors
------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}

module Agda.Utils.Impossible where

import Control.Exception as E

-- | \"Impossible\" errors, annotated with a file name and a line
-- number corresponding to the source code location of the error.

data Impossible

  = Impossible  String Integer
    -- ^ We reached a program point which should be unreachable.

  | Unreachable String Integer
    -- ^ @Impossible@ with a different error message.
    --   Used when we reach a program point which can in principle
    --   be reached, but not for a certain run.

  | ImpMissingDefinitions [String] String
    -- ^ We reached a program point without all the required
    -- primitives or BUILTIN to proceed forward.
    -- @MissingDefinitions needed forthis@

instance Show Impossible where
  show (Impossible file line) = unlines
    [ "An internal error has occurred. Please report this as a bug."
    , "Location of the error: " ++ file ++ ":" ++ show line
    ]
  show (Unreachable file line) = unlines
    [ "We reached a program point we did not want to reach."
    , "Location of the error: " ++ file ++ ":" ++ show line
    ]
  show (ImpMissingDefinitions needed forthis) = unlines
    [ "The following builtins or primitives need to be bound to use " ++ forthis ++ ":"]
    ++ unwords needed

instance Exception Impossible

-- | Abort by throwing an \"impossible\" error. You should not use
-- this function directly. Instead use the macro in @undefined.h@.

throwImpossible :: Impossible -> a
throwImpossible = throw

-- | Catch an \"impossible\" error, if possible.

catchImpossible :: IO a -> (Impossible -> IO a) -> IO a
catchImpossible = E.catch
