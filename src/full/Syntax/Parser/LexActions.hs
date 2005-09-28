{-# OPTIONS -cpp #-}

{-| This module contains the building blocks used to construct the lexer.
-}
module Syntax.Parser.LexActions
    ( -- * Main function
      lexToken
      -- * Lex actions
    , token
    , withRange, withRange', withRange_
    , begin, endWith
    , begin_, end_
      -- * Lex predicates
    , notFollowedBy
    ) where

import Data.List (isPrefixOf)

#ifndef __HADDOCK__
import {-# SOURCE #-} Syntax.Parser.Lexer
#endif

import Syntax.Parser.Alex
import Syntax.Parser.Monad
import Syntax.Parser.Tokens
import Syntax.Position

import Utils.Tuple
import Utils.Unicode

{--------------------------------------------------------------------------
    Scan functions
 --------------------------------------------------------------------------}

-- | Called at the end of a file. Returns 'TkEOF'.
returnEOF :: AlexInput -> Parser Token
returnEOF inp =
    do  setLastPos $ lexPos inp
	setPrevToken "<EOF>"
	return TkEOF

-- | Set the current input and lex a new token (calls 'lexToken').
skipTo :: AlexInput -> Parser Token
skipTo inp = setLexInput inp >> lexToken

{-| Scan the input to find the next token. Calls
    'Syntax.Parser.Lexer.alexScan'.  This is the main lexing function where all
    the work happens.  The function 'Syntax.Parser.Lexer.lexer', used by the
    parser is the continuation version of this function.
-}
lexToken :: Parser Token
lexToken =
    do	inp <- getLexInput
	ls:_ <- getLexState
	case alexScan (foolAlex inp) ls of
	    AlexEOF			-> returnEOF inp
	    AlexError _			-> parseError "Lexical error"
	    AlexSkip inp' len		-> skipTo (newInput inp inp' len)
	    AlexToken inp' len action	-> action inp (newInput inp inp' len) len
		
-- | Use the input string from the previous input (with the appropriate
--   number of characters dropped) instead of the fake input string that
--   was given to Alex (with unicode characters removed).
newInput :: PreviousInput -> CurrentInput -> TokenLength -> CurrentInput
newInput inp inp' len =
    case drop (len - 1) (lexInput inp) of
	c:s'	-> inp' { lexInput    = s'
			, lexPrevChar = c
			}

-- | Alex can't handle unicode characters. To solve this we translate all
--   unicode identifiers to @z@ and all unicode operator characters to @+@.
--   It is important that there aren't any keywords containing @z@ or @+@.
foolAlex :: AlexInput -> AlexInput
foolAlex inp = inp { lexInput = map fool $ lexInput inp }
    where
	fool c
	    | isUnicodeId c = 'z'
	    | isUnicodeOp c = '+'
	    | otherwise	    = c

{--------------------------------------------------------------------------
    Lex actions
 --------------------------------------------------------------------------}

-- | The most general way of lexing a token.
token :: (String -> Parser tok) -> LexAction tok
token action inp inp' len =
    do  setLexInput inp'
	setPrevToken t
	setLastPos $ lexPos inp
	action t
    where
	t = take len $ lexInput inp

-- | Build a token from a 'Range' and the lexed string.
withRange :: ((Range,String) -> tok) -> LexAction tok
withRange f = token $ \s ->
		do  r <- getParseRange
		    return $ f (r,s)

-- | Like 'withRange', but applies a function to the string.
withRange' :: (String -> a) -> ((Range,a) -> tok) -> LexAction tok
withRange' f t = withRange (t . (id -*- f))

-- | Build a token without looking at the lexed string.
withRange_ :: (Range -> r) -> LexAction r
withRange_ f = withRange (f . fst)

-- | Enter a new state without consuming any input.
begin :: LexState -> LexAction Token
begin code _ _ _ =
    do	pushLexState code
	lexToken

-- | Enter a new state throwing away the current lexeme.
begin_ :: LexState -> LexAction Token
begin_ code _ inp' _ =
    do	pushLexState code
	skipTo inp'

-- | Exit the current state throwing away the current lexeme.
end_ :: LexAction Token
end_ _ inp' _ =
    do	popLexState
	skipTo inp'

-- | Exit the current state and perform the given action.
endWith :: LexAction a -> LexAction a
endWith a inp inp' n =
    do	popLexState
	a inp inp' n

{--------------------------------------------------------------------------
    Predicates
 --------------------------------------------------------------------------}

-- | True when the given character is not the next character of the input string.
notFollowedBy :: Char -> LexPredicate
notFollowedBy c' _ _ _ inp =
    case lexInput inp of
	[]  -> True
	c:_ -> c /= c'

