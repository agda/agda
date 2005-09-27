
{-| This module defines the things required by Alex and some other
    Alex related things.
-}
module Syntax.Parser.Alex
    ( -- * Alex requirements
      AlexInput(..)
    , alexInputPrevChar
    , alexGetChar
      -- * Lex actions
    , LexAction, LexPredicate
    , PreviousInput, CurrentInput, TokenLength
      -- * Monad operations
    , getLexInput, setLexInput
    )
    where

import Control.Monad.State

import Syntax.Position
import Syntax.Parser.Monad

import Utils.Monad

-- | This is what the lexer manipulates.
data AlexInput = AlexInput
		    { lexPos	    :: !Position    -- ^ current position
		    , lexInput	    :: String	    -- ^ current input
		    , lexPrevChar   :: !Char	    -- ^ previously read character
		    }

-- | Get the previously lexed character. Same as 'lexPrevChar'. Alex needs this
--   to be defined to handle \"patterns with a left-context\".
alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = lexPrevChar

-- | Lex a character. No surprises.
alexGetChar :: AlexInput -> Maybe (Char, AlexInput)
alexGetChar	(AlexInput { lexInput = []  })	= Nothing
alexGetChar inp@(AlexInput { lexInput = c:s })	=
    Just (c, inp { lexInput	= s
		 , lexPos	= movePos (lexPos inp) c
		 , lexPrevChar	= c
		 }
	 )

{--------------------------------------------------------------------------
    Monad operations
 --------------------------------------------------------------------------}

getLexInput :: Parser AlexInput
getLexInput = getInp <$> get
    where
	getInp s = AlexInput
		    { lexPos	    = parsePos s
		    , lexInput	    = parseInp s
		    , lexPrevChar   = parsePrevChar s
		    }

setLexInput :: AlexInput -> Parser ()
setLexInput inp = modify upd
    where
	upd s = s { parsePos	    = lexPos inp
		  , parseInp	    = lexInput inp
		  , parsePrevChar   = lexPrevChar inp
		  }

{--------------------------------------------------------------------------
    Lex actions
 --------------------------------------------------------------------------}

type PreviousInput  = AlexInput
type CurrentInput   = AlexInput
type TokenLength    = Int

-- | In the lexer, regular expressions are associated with lex actions who's
--   task it is to construct the tokens.
type LexAction r    = PreviousInput -> CurrentInput -> TokenLength -> Parser r

-- | Sometimes regular expressions aren't enough. Alex provides a way to do
--   arbitrary computations to see if the input matches. This is done with a
--   lex predicate.
type LexPredicate   = () -> PreviousInput -> TokenLength -> CurrentInput -> Bool

