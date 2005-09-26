
module Syntax.Parser.Lexer where

import Syntax.Parser.Alex
import Syntax.Parser.Monad
import Syntax.Parser.Tokens

alexScan :: AlexInput -> LexState -> AlexReturn (LexAction Token)

data AlexReturn	r
	= AlexEOF
	| AlexError !AlexInput
	| AlexSkip !AlexInput !TokenLength
	| AlexToken !AlexInput !TokenLength r

layout :: LexState

