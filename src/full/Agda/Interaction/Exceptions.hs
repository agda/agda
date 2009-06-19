
{-| This module defines the exception handler.
-}
module Agda.Interaction.Exceptions where

import Control.OldException
import Control.Monad.Trans
import System.Exit
import qualified System.IO.UTF8 as UTF8

import Agda.Syntax.Position
import Agda.Syntax.Parser		    ( ParseError(..)	       )
import Agda.Syntax.Concrete.Definitions  ( DeclarationException(..) )

handleParseException :: (ParseError -> IO a) -> ParseError -> IO a
handleParseException crash e = crash e

handleDeclarationException :: (DeclarationException -> IO a) -> DeclarationException -> IO a
handleDeclarationException crash e = crash e

failOnException :: (Range -> String -> IO a) -> IO a -> IO a
failOnException h m = m `catchDyn` handleParseException handler
		        `catchDyn` handleDeclarationException handler
    where
	handler x = h (getRange x) (show x)

