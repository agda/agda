{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Interaction.ExitCode (
  AgdaError(..),
  agdaErrorToInt,
  agdaErrorFromInt,
  exitSuccess,
  exitAgdaWith)
  where

import System.Exit (exitSuccess, exitWith, ExitCode(ExitFailure))

data AgdaError = UnknownError      -- ^ 1
               | TCMError          -- ^ 42
               | OptionError       -- ^ 71
               | CommandError      -- ^ 113
               | ImpossibleError   -- ^ 154
               deriving (Show, Eq, Enum, Bounded)

agdaErrorToInt :: AgdaError -> Int
agdaErrorToInt UnknownError    = 1
agdaErrorToInt TCMError        = 42
agdaErrorToInt OptionError     = 71
agdaErrorToInt CommandError    = 113
agdaErrorToInt ImpossibleError = 154

-- ^ Return the error corresponding to an exit code from the
--   Agda process
agdaErrorFromInt :: Int -> Maybe AgdaError
agdaErrorFromInt = -- We implement this in a somewhat more inefficient
                   -- way for the sake of consistency
                   flip lookup [(agdaErrorToInt error, error)
                               | error  <- [minBound..maxBound]
                               ]

exitAgdaWith :: AgdaError -> IO a
exitAgdaWith = exitWith . ExitFailure . agdaErrorToInt
