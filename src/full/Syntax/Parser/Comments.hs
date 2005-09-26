
module Syntax.Parser.Comments
    where

import Syntax.Parser.LexActions
import Syntax.Parser.Monad
import Syntax.Parser.Tokens
import Syntax.Parser.Alex

-- | Nested comments require traversing by hand, since they can't be parsed
--   using regular expressions.
nestedComment :: LexAction Token
nestedComment (p,_,_) i1 n =
	go 1 i1
    where
	go 0 input = do	setLexInput input
			scanToken
	go n input =
	    case alexGetChar input of
		Nothing		-> err
		Just (c,input)	->
		    case c of
			'-' -> case alexGetChar input of
			    Nothing		-> err
			    Just ('}', input)	-> go (n-1) input
			    Just (c, _)         -> go n input
			'{' -> case alexGetChar input of
			    Nothing		-> err
			    Just ('-',input')	-> go (n+1) input'
			    Just (c,input)	-> go n input
			c -> go n input

        err = parseErrorAt p "Unterminated `{-'"

