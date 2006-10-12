
module Syntax.Parser.Lexer where

import Syntax.Parser.Alex
import Syntax.Parser.Monad
import Syntax.Parser.Tokens

alexScan :: AlexInput -> Int -> AlexReturn (LexAction Token)

data AlexReturn	r
	= AlexEOF
	| AlexError !AlexInput
	| AlexSkip !AlexInput !Int
	| AlexToken !AlexInput !Int r

bol, layout, empty_layout :: LexState

