
{-| This module defines the exception handler.
-}
module Agda.Interaction.Exceptions where

import Prelude hiding (catch)
import Control.Exception
import Control.Monad.Trans
import System.Exit
import qualified System.IO.UTF8 as UTF8

import Agda.Syntax.Position
import Agda.Syntax.Parser ( ParseError(..) )

handleParseException :: (ParseError -> IO a) -> ParseError -> IO a
handleParseException crash e = crash e

-- | Note that 'failOnException' only catches 'ParseError's.

failOnException :: (Range -> String -> IO a) -> IO a -> IO a
failOnException h m = m `catch` handleParseException handler
    where
	handler x = h (getRange x) (show x)

