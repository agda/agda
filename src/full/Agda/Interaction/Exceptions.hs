{-| This module defines the exception handler.
-}
module Agda.Interaction.Exceptions where

import Prelude
import Control.Exception as E

import Agda.Syntax.Position
import Agda.Syntax.Parser ( ParseError )

import Agda.Utils.Pretty

handleParseException :: (ParseError -> IO a) -> ParseError -> IO a
handleParseException crash e = crash e

-- | Note that 'failOnException' only catches 'ParseError's.

failOnException :: (Range -> Doc -> IO a) -> IO a -> IO a
failOnException h m = m `E.catch` handleParseException handler
    where
        handler x = h (getRange x) (pretty x)
