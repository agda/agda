
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
import Syntax.Parser.LookAhead

-- | Manually lexing a block comment. Assumes an /open comment/ has been lexed.
--   In the end the comment is discarded and 'lexToken' is called to lex a real
--   token.
nestedComment :: LexAction Token
nestedComment inp inp' _ =
    do	setLexInput inp'
	runLookAhead err (scan 1)
	lexToken
    where
	scan 0 = sync
	scan n =
	    do	c1  <- nextChar
		inp <- getInput
		case c1 of
		    '-'	-> do c2 <- nextChar
			      case c2 of
				'}' -> scan (n - 1)
				_   -> setInput inp >> scan n
		    '{'	-> do c2 <- nextChar
			      case c2 of
				'-' -> scan (n + 1)
				_   -> setInput inp >> scan n
		    _	-> scan n

        err _ = liftP $ parseErrorAt (lexPos inp) "Unterminated '{-'"

