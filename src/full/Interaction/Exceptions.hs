
{-| This module defines the exception handler.
-}
module Interaction.Exceptions where

import Control.Exception
import Control.Monad.Trans
import System.Exit

import Syntax.Position
import Syntax.Parser			     ( ParseError(..)		)
import Syntax.Concrete.Definitions	     ( DeclarationException(..) )
-- import Syntax.Concrete.Operators	     ( OperatorException(..)	)
-- import Syntax.Translation.ConcreteToAbstract ( ToAbstractException(..)	)

crash :: Range -> String -> IO b
crash r x =
    do	print r
	putStrLn x
	exitWith (ExitFailure 1)

handleParseException :: (ParseError -> IO a) -> ParseError -> IO a
handleParseException crash e = crash e

handleDeclarationException :: (DeclarationException -> IO a) -> DeclarationException -> IO a
handleDeclarationException crash e = crash e

-- handleOperatorException :: (OperatorException -> IO a) -> OperatorException -> IO a
-- handleOperatorException crash e = crash e

-- handleToAbstractException :: (ToAbstractException -> IO a) -> ToAbstractException -> IO a
-- handleToAbstractException crash e = crash e

-- | Crash on exception.
crashOnException :: IO a -> IO a
crashOnException m = failOnException crash m

failOnException :: (Range -> String -> IO a) -> IO a -> IO a
failOnException h m = m `catchDyn` handleParseException handler
		        `catchDyn` handleDeclarationException handler
-- 		        `catchDyn` handleOperatorException handler
-- 		        `catchDyn` handleToAbstractException handler
    where
	handler x = h (getRange x) (show x)

