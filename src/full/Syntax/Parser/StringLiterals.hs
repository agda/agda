{-# OPTIONS -fglasgow-exts #-}

{-| The code to lex string and character literals. Shamelessly stolen
    from ghc.
-}
module Syntax.Parser.StringLiterals where

import Data.Char

import Syntax.Parser.Alex
import Syntax.Parser.Monad
import Syntax.Parser.Tokens
import Syntax.Position

import Utils.List ( maybePrefixMatch )
import Utils.Char ( decDigit, hexDigit, octDigit )

lit_error = parseError "lexical error in string literal"

lex_atom :: LexAction Token
lex_atom = lex_string_tok '"' (curry TkAtom)

lex_string_tok :: Char -> (Range -> String -> a) -> LexAction a
lex_string_tok del mkTok i1 i2 n =
    do	setLexInput i2
	tok <- lex_string del ""
	r <- getParseRange
	return $ mkTok r tok

lex_string :: Char -> String -> Parser String
lex_string del s =
    do	i <- getLexInput
	case alexGetChar i of
	    Nothing -> lit_error

	    Just (c,i) | c == del  ->
		do  setLexInput i
		    return (reverse s)

	    Just ('\\',i)
		| Just ('&',i) <- next ->
		    do setLexInput i
		       lex_string del s
		| Just (c,i) <- next, isSpace c ->
		    do setLexInput i
		       lex_stringgap del s
		where next = alexGetChar i

	    Just _ ->
		do c <- lex_char
		   lex_string del (c:s)

lex_stringgap del s =
    do	c <- getCharOrFail
	case c of
	    '\\'	    -> lex_string del s
	    c | isSpace c   -> lex_stringgap del s
	    _other	    -> lit_error

lex_char :: Parser Char
lex_char =
    do	mc <- getCharOrFail
	case mc of
	    '\\'    -> lex_escape
	    c	    -> return c

lex_escape :: Parser Char
lex_escape =
    do	c <- getCharOrFail
	case c of
	    'a'   -> return '\a'
	    'b'   -> return '\b'
	    'f'   -> return '\f'
	    'n'   -> return '\n'
	    'r'   -> return '\r'
	    't'   -> return '\t'
	    'v'   -> return '\v'
	    '\\'  -> return '\\'
	    '"'   -> return '\"'
	    '\''  -> return '\''
	    '^'   -> do c <- getCharOrFail
			if c >= '@' && c <= '_'
			    then return (chr (ord c - ord '@'))
			    else lit_error

	    'x'   -> readNum isHexDigit 16 hexDigit
	    'o'   -> readNum isOctDigit  8 octDecDigit
	    x | isDigit x -> readNum2 isDigit 10 octDecDigit (octDecDigit x)

	    c1 ->
		do  i <- getLexInput
		    case alexGetChar i of
			Nothing		-> lit_error
			Just (c2,i2)	-> 
			    case alexGetChar i2 of
				Nothing		-> lit_error
				Just (c3,i3)	-> 
				   let str = [c1,c2,c3] in
				   case [ (c,rest) | (p,c) <- silly_escape_chars,
						     Just rest <- [maybePrefixMatch p str] ] of
					  (escape_char,[]):_ -> do
						setLexInput i3
						return escape_char
					  (escape_char,_:_):_ -> do
						setLexInput i2
						return escape_char
					  [] -> lit_error

maybePrefixMatch :: String -> String -> Maybe String
maybePrefixMatch []    rest = Just rest
maybePrefixMatch (_:_) []   = Nothing
maybePrefixMatch (p:pat) (r:rest)
  | p == r    = maybePrefixMatch pat rest
  | otherwise = Nothing

hexDigit :: Char -> Int
hexDigit c | isDigit c = ord c - ord '0'
           | otherwise  = ord (toLower c) - ord 'a' + 10

octDecDigit :: Char -> Int
octDecDigit c = ord c - ord '0'

readNum :: (Char -> Bool) -> Int -> (Char -> Int) -> Parser Char
readNum is_digit base conv =
    do	c <- getCharOrFail
	if is_digit c 
	    then readNum2 is_digit base conv (conv c)
	    else lit_error

readNum2 is_digit base conv i =
    do	input <- getLexInput
	read i input
    where
	read i input =
	    case alexGetChar input of
		Just (c,input') | is_digit c ->
		    read (i*base + conv c) input'
		_other ->
		    do	setLexInput input
			if i >= 0 && i <= 0x10FFFF
			    then return (chr i)
			    else lit_error

silly_escape_chars = [
	("NUL", '\NUL'),
	("SOH", '\SOH'),
	("STX", '\STX'),
	("ETX", '\ETX'),
	("EOT", '\EOT'),
	("ENQ", '\ENQ'),
	("ACK", '\ACK'),
	("BEL", '\BEL'),
	("BS", '\BS'),
	("HT", '\HT'),
	("LF", '\LF'),
	("VT", '\VT'),
	("FF", '\FF'),
	("CR", '\CR'),
	("SO", '\SO'),
	("SI", '\SI'),
	("DLE", '\DLE'),
	("DC1", '\DC1'),
	("DC2", '\DC2'),
	("DC3", '\DC3'),
	("DC4", '\DC4'),
	("NAK", '\NAK'),
	("SYN", '\SYN'),
	("ETB", '\ETB'),
	("CAN", '\CAN'),
	("EM", '\EM'),
	("SUB", '\SUB'),
	("ESC", '\ESC'),
	("FS", '\FS'),
	("GS", '\GS'),
	("RS", '\RS'),
	("US", '\US'),
	("SP", '\SP'),
	("DEL", '\DEL')
	]

getCharOrFail :: Parser Char
getCharOrFail =
    do	i <- getLexInput
	case alexGetChar i of
	    Nothing	-> parseError "unexpected end-of-file in string literal"
	    Just (c,i)	-> do setLexInput i
			      return c

