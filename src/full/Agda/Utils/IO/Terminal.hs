-- | Utilities for interacting with the terminal.

module Agda.Utils.IO.Terminal where

import System.Console.ANSI ( hSupportsANSI )
import System.Environment  ( lookupEnv )
import System.IO           ( stdout )

import Agda.Utils.Monad    ( and2M )

-- | Is the @NO_COLOR@ environment variable unset?
environmentColor :: IO Bool
environmentColor = null <$> lookupEnv "NO_COLOR"

stdoutSupportsANSI :: IO Bool
stdoutSupportsANSI = environmentColor `and2M` hSupportsANSI stdout
