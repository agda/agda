
{-| This module defines the things required by Alex.
-}
module Syntax.Parser.Alex
    ( AlexInput(..)
    , alexInputPrevChar
    , alexGetChar
    )
    where

import Syntax.Position

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

