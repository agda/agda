{-# OPTIONS -cpp #-}

module Syntax.Parser.LexActions
    ( -- * Scan functions
      scanToken
      -- * Lex actions
    , lexToken
    , withRange, withRange', withRange_
    , withLayout
    , begin, endWith
    , begin_, end_
      -- * Lex predicates
    , notFollowedBy, atEOL
#ifdef __HADDOCK__
      -- * Circular dependencies
    , AlexReturn
#endif
    ) where

import Data.List (isPrefixOf)

#ifndef __HADDOCK__
import {-# SOURCE #-} Syntax.Parser.Lexer
#endif

import Syntax.Parser.Alex
import Syntax.Parser.Monad
import Syntax.Parser.Tokens
import Syntax.Position

import Utils.Pairs
import Utils.Unicode

#ifdef __HADDOCK__
-- | Recursive import.
type AlexReturn = Syntax.Parser.Lexer.AlexReturn
#endif

{--------------------------------------------------------------------------
    Scan functions
 --------------------------------------------------------------------------}

-- | Called at the end of a file. Returns 'TkEOF'.
scanEOF :: AlexInput -> Parser Token
scanEOF inp =
    do  setLastPos $ lexPos inp
	setPrevToken "<EOF>"
	return TkEOF

-- | Set the current input and lex a new token (calls 'scanToken').
scanSkip :: AlexInput -> Parser Token
scanSkip inp = setLexInput inp >> scanToken

-- | Scan the input to find the next token. Calls 'Syntax.Parser.Lexer.alexScan'.
scanToken :: Parser Token
scanToken =
    do	inp <- getLexInput
	ls:_ <- getLexState
	case alexScan (foolAlex inp) ls of
	    AlexEOF			-> scanEOF inp
	    AlexError _			-> parseError "Lexical error"
	    AlexSkip inp' len		-> scanSkip (newInput inp inp' len)
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
lexToken :: (String -> Parser tok) -> LexAction tok
lexToken action inp inp' len =
    do  setLexInput inp'
	setPrevToken t
	setLastPos $ lexPos inp
	action t
    where
	t = take len $ lexInput inp

-- | Build a token from a 'Range' and the lexed string.
withRange :: ((Range,String) -> tok) -> LexAction tok
withRange f = lexToken $ \s ->
		do  r <- getParseRange
		    return $ f (r,s)

-- | Like 'withRange', but applies a function to the string.
withRange' :: (String -> a) -> ((Range,a) -> tok) -> LexAction tok
withRange' f t = withRange (t . (id -*- f))

-- | Build a token without looking at the lexed string.
withRange_ :: (Range -> r) -> LexAction r
withRange_ f = withRange (f . fst)

-- | Perform action and enter layout mode.
withLayout :: LexAction r -> LexAction r
withLayout a i1 i2 n =
    do	pushLexState layout
	a i1 i2 n

-- | Enter a new state without consuming any input.
begin :: LexState -> LexAction Token
begin code _ _ _ =
    do	pushLexState code
	scanToken

-- | Enter a new state throwing away the current lexeme.
begin_ :: LexState -> LexAction Token
begin_ code _ inp' _ =
    do	pushLexState code
	scanSkip inp'

-- | Exit the current state throwing away the current lexeme.
end_ :: LexAction Token
end_ _ inp' _ =
    do	popLexState
	scanSkip inp'

-- | Exit the current state and perform the given action.
endWith :: LexAction a -> LexAction a
endWith a inp inp' n =
    do	popLexState
	a inp inp' n

{--------------------------------------------------------------------------
    Predicates
 --------------------------------------------------------------------------}

-- | True when the given character is not the next character of the input string.
--   Used when lexing open braces (should not be followed by @\'-\'@).
notFollowedBy :: Char -> LexPredicate
notFollowedBy c' _ _ _ inp =
    case lexInput inp of
	[]  -> True
	c:_ -> c /= c'

-- | True when we have just lexed a newline.
atEOL :: LexPredicate
atEOL _ _ _ inp = null (lexInput inp) || lexPrevChar inp == '\n'

