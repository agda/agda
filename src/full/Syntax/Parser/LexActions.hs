{-# OPTIONS -cpp #-}

module Syntax.Parser.LexActions
    where

import Data.List (isPrefixOf)

#ifndef __HADDOCK__
import {-# SOURCE #-} Syntax.Parser.Lexer
#endif

import Syntax.Parser.Alex
import Syntax.Parser.Monad
import Syntax.Parser.Tokens
import Syntax.Position

import Utils.Unicode

#ifdef __HADDOCK__
type AlexReturn = Syntax.Parser.Lexer.AlexReturn
#endif

withRange :: (Range -> String -> r) -> LexAction r
withRange f = scanTok $ \s ->
			do  r <- getParseRange
			    return $ f r s

withRange_ :: (Range -> r) -> LexAction r
withRange_ f = withRange (\r _ -> f r)

-- Scan functions ---------------------------------------------------------

scanEOF inp eof =
    do  setLastPos $ lexPos inp
	setPrevToken "EOF"
	return eof

scanError inp = parseError "Lexical error"

scanSkip inp r = setLexInput inp >> r

scanTok action inp inp' len =
    do  setLexInput inp'
	setPrevToken t
	setLastPos $ lexPos inp
	action t
    where
	t = take len $ lexInput inp

scanToken :: Parser Token
scanToken =
    do	inp <- getLexInput
	ls:_ <- getLexState
	case alexScan (foolAlex inp) ls of
	    AlexEOF			-> scanEOF inp TkEOF
	    AlexError _			-> scanError inp
	    AlexSkip inp' len		-> scanSkip (newInput inp inp' len)
						    scanToken
	    AlexToken inp' len action	-> action inp (newInput inp inp' len) len
		

newInput (_,s,_) (pn,_,_) len =
    case drop (len - 1) s of
	c:s'	-> (pn, s', c)

foolAlex (pn,s,c) = (pn, map fool s, c)
    where
	fool c
	    | isUnicodeId c = 'z'
	    | isUnicodeOp c = '+'
	    | otherwise	    = c

-- States

begin :: LexState -> LexAction Token
begin code _ _ _ =
    do	pushLexState code
	scanToken

begin_ :: LexState -> LexAction Token
begin_ code _ inp' _ =
    do	pushLexState code
	scanSkip inp' scanToken

end_ :: LexAction Token
end_ _ inp' _ =
    do	popLexState
	scanSkip inp' scanToken

popAnd :: LexAction a -> LexAction a
popAnd a inp inp' n =
    do	popLexState
	a inp inp' n

notFollowedBy :: Char -> AlexInput -> AlexInput -> Int -> AlexInput -> Bool
notFollowedBy c _ _ _ (_,i,_) =
    null i || head i /= c

atEOL _ _ _ (_,i,c) = null i || c == '\n'

isBeginCode _ _ _ (_,i,_) = null i || ("\\begin{code}" `isPrefixOf` i)

withLayout :: LexAction r -> LexAction r
withLayout a i1 i2 n =
    do	pushLexState layout
	a i1 i2 n

