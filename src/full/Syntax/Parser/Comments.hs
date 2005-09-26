
{-| This module defines the lex action to lex nested comments. As is well-known
    this cannot be done by regular expressions (which, incidently, is probably
    the reason why C-comments don't nest).

    When scanning nested comments we simply keep track of the nesting level,
    counting up for /open comments/ and down for /close comments/.
-}
module Syntax.Parser.Comments
    where

import Syntax.Parser.LexActions
import Syntax.Parser.Monad
import Syntax.Parser.Tokens
import Syntax.Parser.Alex

-- | Manually lexing a block comment. Assumes an /open comment/ has been lexed.
--   In the end the comment is discarded and 'lexToken' is called to lex a real
--   token.
nestedComment :: LexAction Token
nestedComment inp inp' n =
	go 1 inp'
    where
	go 0 inp = do setLexInput inp
		      lexToken
	go n inp =
	    case alexGetChar inp of
		Nothing		-> err
		Just (c,inp)	->
		    case c of
			'-' -> case alexGetChar inp of
				Nothing		-> err
				Just ('}',inp') -> go (n-1) inp'
				Just (c, _)	-> go n inp
			'{' -> case alexGetChar inp of
				Nothing		-> err
				Just ('-',inp') -> go (n+1) inp'
				Just (c,inp)	-> go n inp
			c -> go n inp

        err = parseErrorAt (lexPos inp) "Unterminated `{-'"

