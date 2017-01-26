------------------------------------------------------------------------
-- | An interface for reporting \"impossible\" errors
------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}

module Agda.Utils.Impossible where

import Control.Exception as E
import Data.Typeable ( Typeable )

-- | \"Impossible\" errors, annotated with a file name and a line
-- number corresponding to the source code location of the error.

data Impossible

  = Impossible  String Integer
    -- ^ We reached a program point which should be unreachable.

  | Unreachable String Integer
    -- ^ @Impossible@ with a different error message.
    --   Used when we reach a program point which can in principle
    --   be reached, but not for a certain run.

  deriving Typeable

instance Show Impossible where
  show (Impossible file line) = unlines
    [ "An internal error has occurred. Please report this as a bug."
    , "Location of the error: " ++ file ++ ":" ++ show line
    ]
  show (Unreachable file line) = unlines
    [ "We reached a program point we did not want to reach."
    , "Location of the error: " ++ file ++ ":" ++ show line
    ]

instance Exception Impossible

-- | Abort by throwing an \"impossible\" error. You should not use
-- this function directly. Instead use the macro in @undefined.h@.

throwImpossible :: Impossible -> a
throwImpossible = throw

-- | Catch an \"impossible\" error, if possible.

catchImpossible :: IO a -> (Impossible -> IO a) -> IO a
catchImpossible = E.catch
