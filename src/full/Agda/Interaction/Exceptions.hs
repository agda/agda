
{-| This module defines the exception handler.
-}
module Agda.Interaction.Exceptions where

import Control.Exception
import Control.Monad.Trans
import System.Exit
import qualified System.IO.UTF8 as UTF8

import Agda.Syntax.Position
import Agda.Syntax.Parser		    ( ParseError(..)	       )
import Agda.Syntax.Concrete.Definitions  ( DeclarationException(..) )

crash :: Range -> String -> IO b
crash r x =
    do	UTF8.print r
	UTF8.putStrLn x
	exitWith (ExitFailure 1)

handleParseException :: (ParseError -> IO a) -> ParseError -> IO a
handleParseException crash e = crash e

handleDeclarationException :: (DeclarationException -> IO a) -> DeclarationException -> IO a
handleDeclarationException crash e = crash e

-- | Crash on exception.
crashOnException :: IO a -> IO a
crashOnException m = failOnException crash m

failOnException :: (Range -> String -> IO a) -> IO a -> IO a
failOnException h m = m `catchDyn` handleParseException handler
		        `catchDyn` handleDeclarationException handler
    where
	handler x = h (getRange x) (show x)

