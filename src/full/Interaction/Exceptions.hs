
{-| This module defines the exception handler.
-}
module Interaction.Exceptions where

import Control.Exception
import Control.Monad.Trans
import System.Exit

import Syntax.Position
import Syntax.Parser		    ( ParseError(..)	       )
import Syntax.Concrete.Definitions  ( DeclarationException(..) )

crash :: Range -> String -> IO b
crash r x =
    do	print r
	putStrLn x
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

