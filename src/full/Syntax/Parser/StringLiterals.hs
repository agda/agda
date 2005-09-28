{-# OPTIONS -fglasgow-exts #-}

{-| The code to lex string and character literals. Basically the same code
    as in GHC.
-}
module Syntax.Parser.StringLiterals
    ( litString, litChar
    ) where

import Control.Monad.State
import Data.Char

import Syntax.Parser.Alex
import Syntax.Parser.Monad
import Syntax.Parser.Tokens
import Syntax.Position

import Utils.List ( maybePrefixMatch )
import Utils.Char ( decDigit, hexDigit, octDigit )

{--------------------------------------------------------------------------
    Exported actions
 --------------------------------------------------------------------------}

-- | Lex a string literal. Assumes that a double quote has been lexed.
litString :: LexAction Token
litString = stringToken '"' (return . TokLitString)

{-| Lex a character literal. Assumes that a single quote has been lexed.  A
    character literal is lexed in exactly the same way as a string literal.
    Only before returning the token do we check that the lexed string is of
    length 1. This is maybe not the most efficient way of doing things, but on
    the other hand it will only be inefficient if there is a lexical error.
-}
litChar :: LexAction Token
litChar = stringToken '\'' $ \(r,s) ->
	    do	case s of
		    [c]	-> return $ TokLitChar (r,c)
		    _	-> runLitM $ litError
			    "character literal must contain a single character"


{--------------------------------------------------------------------------
    The literal monad
 --------------------------------------------------------------------------}

{-| When lexing string literals we need to do some looking ahead. For this
    purpose we wrap an extra state monad around the parse monad to keep track
    of the input we're currently looking at.
-}
type LitM = StateT AlexInput Parser


getInput :: LitM AlexInput
getInput = get


setInput :: AlexInput -> LitM ()
setInput = put


-- | Lex a character from the current input. Does not affect the 'ParseState'.
nextChar :: LitM Char
nextChar =
    do	inp <- getInput
	case alexGetChar inp of
	    Nothing	    -> eofError
	    Just (c,inp')   ->
		do  setInput inp'
		    return c


-- | Save the current input in the 'ParseState'.
sync :: LitM ()
sync =
    do	inp <- getInput
	lift $ setLexInput inp


-- | Undo look-ahead. Restores the input from the 'ParseState'.
rollback :: LitM ()
rollback =
    do	inp <- lift getLexInput
	setInput inp


-- | Lex a character from the current input and 'sync'.
getNextChar :: LitM Char
getNextChar =
    do	c <- nextChar
	sync
	return c


-- | Run a 'LitM' computation.
runLitM :: LitM a -> Parser a
runLitM m =
    do	inp <- getLexInput
	evalStateT m inp

{--------------------------------------------------------------------------
    Errors
 --------------------------------------------------------------------------}

-- | Custom error function.
litError :: String -> LitM a
litError msg =
    do	sync
	lift $ lexError $
	    "Lexical error in string or character literal: " ++ msg


-- | End of file error. Thrown by 'nextChar'.
eofError :: LitM a
eofError = litError "unexpected end of file."


{--------------------------------------------------------------------------
    The meat
 --------------------------------------------------------------------------}

-- | The general function to lex a string or character literal token. The
--   character argument is the delimiter (@\"@ for strings and @\'@ for
--   characters).
stringToken :: Char -> ((Range,String) -> Parser tok) -> LexAction tok
stringToken del mkTok inp inp' n =
    do	setLexInput inp'
	tok <- runLitM $ lexString del ""
	r   <- getParseRange
	mkTok (r,tok)


-- | This is where the work happens. The string argument is an accumulating
--   parameter for the string being lexed.
lexString :: Char -> String -> LitM String
lexString del s =

    do	c <- nextChar
	case c of

	    c | c == del  -> sync >> return (reverse s)

	    '\\' ->
		do  c' <- nextChar
		    case c' of
			'&'		-> sync >> lexString del s
			c | isSpace c	-> sync >> lexStringGap del s
			_		-> normalChar

	    _ -> normalChar
    where
	normalChar =
	    do	rollback
		c <- lexChar
		lexString del (c:s)


-- | A string gap consists of whitespace (possibly including line breaks)
--   enclosed in backslashes. The gap is not part of the resulting string.
lexStringGap :: Char -> String -> LitM String
lexStringGap del s =
    do	c <- getNextChar
	case c of
	    '\\'	    -> lexString del s
	    c | isSpace c   -> lexStringGap del s
	    _		    -> litError "non-space in string gap."

-- | Lex a single character.
lexChar :: LitM Char
lexChar =
    do	c <- getNextChar
	case c of
	    '\\'    -> lexEscape
	    _	    -> return c

-- | Lex an escaped character. Assumes the backslash has been lexed.
lexEscape :: LitM Char
lexEscape =
    do	c <- getNextChar
	case c of
	    'a'	    -> return '\a'
	    'b'	    -> return '\b'
	    'f'	    -> return '\f'
	    'n'	    -> return '\n'
	    'r'	    -> return '\r'
	    't'	    -> return '\t'
	    'v'	    -> return '\v'
	    '\\'    -> return '\\'
	    '"'	    -> return '\"'
	    '\''    -> return '\''
	    '^'	    -> do c <- getNextChar
			  if c >= '@' && c <= '_'
			    then return (chr (ord c - ord '@'))
			    else litError "invalid control character."

	    'x'	    -> readNum isHexDigit 16 hexDigit
	    'o'	    -> readNum isOctDigit  8 octDigit
	    x | isDigit x
		    -> readNumAcc isDigit 10 decDigit (decDigit x)

	    c1 ->
		do  c2	<- nextChar
		    inp <- getInput -- we might not need c3 so let's save
				    -- this input
		    c3	<- nextChar
		    let -- The escape codes are at most 3 characters long
			str	    = [c1,c2,c3]
			-- Match str against the escape codes. Return the
			-- corresponding character together with any left
			-- over characters in str.
			matchEscape =
			    [ (c,rest)
			    | (esc,c)   <- sillyEscapeChars
			    , Just rest <- [maybePrefixMatch esc str]
			    ]
		    case matchEscape of

			-- We found a code of length 3 (nothing left of str)
			(esc,[]):_  -> sync >> return esc

			-- We found a code of length 2, so we have to unlex
			-- the last character (restore the input saved above)
			(esc,_:_):_ ->
			    do	setInput inp
				sync
				return esc

			-- No matching code
			[]	    -> litError "bad escape code."


-- | Read a number in the specified base.
readNum :: (Char -> Bool) -> Int -> (Char -> Int) -> LitM Char
readNum isDigit base conv =
    do	c <- getNextChar
	if isDigit c 
	    then readNumAcc isDigit base conv (conv c)
	    else litError "non-digit in numeral."

-- | Same as 'readNum' but with an accumulating parameter.
readNumAcc :: (Char -> Bool) -> Int -> (Char -> Int) -> Int -> LitM Char
readNumAcc isDigit base conv i = scan i
    where
	scan i =
	    do	c <- nextChar
		case c of
		    c | isDigit c -> scan (i*base + conv c)
		    _		  ->
			do  sync
			    if i >= ord minBound && i <= ord maxBound
				then return (chr i)
				else litError "character literal out of bounds."

-- | The escape codes.
sillyEscapeChars :: [(String, Char)]
sillyEscapeChars = [
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

