
{-| This module defines the exception handler.
-}
module Interaction.Exceptions where

import Control.Exception
import Control.Monad.Trans
import System.Exit

import Syntax.Position
import Syntax.Parser			     ( ParseError(..)		)
import Syntax.Concrete.Definitions	     ( DeclarationException(..) )
import Syntax.Concrete.Fixity		     ( InfixException(..)	)
import Syntax.Scope			     ( ScopeException(..)	)
import Syntax.Translation.ConcreteToAbstract ( ToAbstractException(..)	)
import Interaction.Imports		     ( ImportException(..)	)

crash :: (HasRange a, Show a) => a -> IO b
crash x =
    do	print $ getRange x
	print x
	exitWith (ExitFailure 1)

handleParseException :: ParseError -> IO a
handleParseException e = crash e

handleDeclarationException :: DeclarationException -> IO a
handleDeclarationException e = crash e

handleInfixException :: InfixException -> IO a
handleInfixException e = crash e

handleScopeException :: ScopeException -> IO a
handleScopeException e = crash e

handleToAbstractException :: ToAbstractException -> IO a
handleToAbstractException e = crash e

handleImportException :: ImportException -> IO a
handleImportException e = crash e

-- | Crash on exception.
crashOnException :: IO a -> IO a
crashOnException m = m `catchDyn` handleParseException
		       `catchDyn` handleDeclarationException
		       `catchDyn` handleScopeException
		       `catchDyn` handleInfixException
		       `catchDyn` handleToAbstractException
		       `catchDyn` handleImportException

