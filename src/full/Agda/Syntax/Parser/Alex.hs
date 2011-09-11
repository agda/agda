
{-| This module defines the things required by Alex and some other
    Alex related things.
-}
module Agda.Syntax.Parser.Alex
    ( -- * Alex requirements
      AlexInput(..)
    , alexInputPrevChar
    , alexGetChar, alexGetByte
      -- * Lex actions
    , LexAction, LexPredicate
    , (.&&.), (.||.), not'
    , PreviousInput, CurrentInput, TokenLength
      -- * Monad operations
    , getLexInput, setLexInput
    )
    where

import Control.Arrow
import Control.Monad.State
import Data.Word

import Agda.Syntax.Position
import Agda.Syntax.Parser.Monad

import Agda.Utils.Monad

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
--
-- This function is used by Alex 2.
alexGetChar :: AlexInput -> Maybe (Char, AlexInput)
alexGetChar (AlexInput { lexInput = []  }) = Nothing
alexGetChar (AlexInput { lexInput = c:s, lexPos = p }) =
    Just (c, AlexInput
		 { lexInput	= s
		 , lexPos	= movePos p c
		 , lexPrevChar	= c
		 }
	 )

-- | A variant of 'alexGetChar'.
--
-- This function is used by Alex 3.
alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte ai =
  -- Note that we ensure that every character presented to Alex fits
  -- in seven bits.
  (fromIntegral . fromEnum *** id) <$> alexGetChar ai

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
type LexPredicate   = ([LexState], ParseFlags) -> PreviousInput -> TokenLength -> CurrentInput -> Bool

-- | Conjunction of 'LexPredicate's.
(.&&.) :: LexPredicate -> LexPredicate -> LexPredicate
p1 .&&. p2 = \x y z u -> p1 x y z u && p2 x y z u

-- | Disjunction of 'LexPredicate's.
(.||.) :: LexPredicate -> LexPredicate -> LexPredicate
p1 .||. p2 = \x y z u -> p1 x y z u || p2 x y z u

-- | Negation of 'LexPredicate's.
not' :: LexPredicate -> LexPredicate
not' p = \x y z u -> not (p x y z u)
