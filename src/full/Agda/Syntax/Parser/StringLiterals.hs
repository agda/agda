{-| The code to lex string and character literals. Basically the same code
    as in GHC.
-}
module Agda.Syntax.Parser.StringLiterals
    ( litString, litChar
    ) where

import Data.Char

import Agda.Syntax.Parser.Alex
import Agda.Syntax.Parser.Monad
import Agda.Syntax.Parser.Tokens
import Agda.Syntax.Parser.LookAhead
import Agda.Syntax.Position
import Agda.Syntax.Literal

import Agda.Utils.Tuple  ( (-*-) )

{--------------------------------------------------------------------------
    Exported actions
 --------------------------------------------------------------------------}

-- | Lex a string literal. Assumes that a double quote has been lexed.
litString :: LexAction Token
litString = stringToken '"' (\i s ->
              return $ TokLiteral $ LitString (getRange i) s)

{-| Lex a character literal. Assumes that a single quote has been lexed.  A
    character literal is lexed in exactly the same way as a string literal.
    Only before returning the token do we check that the lexed string is of
    length 1. This is maybe not the most efficient way of doing things, but on
    the other hand it will only be inefficient if there is a lexical error.
-}
litChar :: LexAction Token
litChar = stringToken '\'' $ \i s ->
            do  case s of
                    [c] -> return $ TokLiteral $ LitChar (getRange i) c
                    _   -> lexError
                            "character literal must contain a single character"


{--------------------------------------------------------------------------
    Errors
 --------------------------------------------------------------------------}

-- | Custom error function.
litError :: String -> LookAhead a
litError msg =
    do  sync
        liftP $ lexError $
            "Lexical error in string or character literal: " ++ msg


{--------------------------------------------------------------------------
    The meat
 --------------------------------------------------------------------------}

-- | The general function to lex a string or character literal token. The
--   character argument is the delimiter (@\"@ for strings and @\'@ for
--   characters).
stringToken :: Char -> (Interval -> String -> Parser tok) -> LexAction tok
stringToken del mkTok inp inp' n =
    do  setLastPos (backupPos $ lexPos inp')
        setLexInput inp'
        -- TODO: Should setPrevToken be run here? Compare with
        -- Agda.Syntax.Parser.LexActions.token.
        tok <- runLookAhead litError $ lexString del ""
        i   <- getParseInterval
        mkTok i tok


-- | This is where the work happens. The string argument is an accumulating
--   parameter for the string being lexed.
lexString :: Char -> String -> LookAhead String
lexString del s =

    do  c <- nextChar
        case c of

            c | c == del  -> sync >> return (reverse s)

            '\\' ->
                do  c' <- nextChar
                    case c' of
                        '&'             -> sync >> lexString del s
                        c | isSpace c   -> sync >> lexStringGap del s
                        _               -> normalChar

            _ -> normalChar
    where
        normalChar =
            do  rollback
                c <- lexChar
                lexString del (c:s)


-- | A string gap consists of whitespace (possibly including line breaks)
--   enclosed in backslashes. The gap is not part of the resulting string.
lexStringGap :: Char -> String -> LookAhead String
lexStringGap del s =
    do  c <- eatNextChar
        case c of
            '\\'            -> lexString del s
            c | isSpace c   -> lexStringGap del s
            _               -> lookAheadError "non-space in string gap"

-- | Lex a single character.
lexChar :: LookAhead Char
lexChar =
    do  c <- eatNextChar
        case c of
            '\\'    -> lexEscape
            _       -> return c

-- | Lex an escaped character. Assumes the backslash has been lexed.
lexEscape :: LookAhead Char
lexEscape =
    do  c <- eatNextChar
        case c of
            '^'     -> do c <- eatNextChar
                          if c >= '@' && c <= '_'
                            then return (chr (ord c - ord '@'))
                            else lookAheadError "invalid control character"

            'x'     -> readNum isHexDigit 16 digitToInt
            'o'     -> readNum isOctDigit  8 digitToInt
            x | isDigit x
                    -> readNumAcc isDigit 10 digitToInt (digitToInt x)

            c ->
                -- Try to match the input (starting with c) against the
                -- silly escape codes.
                do  esc <- match' c (map (id -*- return) sillyEscapeChars)
                                    (lookAheadError "bad escape code")
                    sync
                    return esc

-- | Read a number in the specified base.
readNum :: (Char -> Bool) -> Int -> (Char -> Int) -> LookAhead Char
readNum isDigit base conv =
    do  c <- eatNextChar
        if isDigit c
            then readNumAcc isDigit base conv (conv c)
            else lookAheadError "non-digit in numeral"

-- | Same as 'readNum' but with an accumulating parameter.
readNumAcc :: (Char -> Bool) -> Int -> (Char -> Int) -> Int -> LookAhead Char
readNumAcc isDigit base conv i = scan i
    where
        scan i =
            do  inp <- getInput
                c   <- nextChar
                case c of
                    c | isDigit c -> scan (i*base + conv c)
                    _             ->
                        do  setInput inp
                            sync
                            if i >= ord minBound && i <= ord maxBound
                                then return (chr i)
                                else lookAheadError "character literal out of bounds"

-- | The escape codes.
sillyEscapeChars :: [(String, Char)]
sillyEscapeChars =
    [ ("a", '\a')
    , ("b", '\b')
    , ("f", '\f')
    , ("n", '\n')
    , ("r", '\r')
    , ("t", '\t')
    , ("v", '\v')
    , ("\\", '\\')
    , ("\"", '\"')
    , ("'", '\'')
    , ("NUL", '\NUL')
    , ("SOH", '\SOH')
    , ("STX", '\STX')
    , ("ETX", '\ETX')
    , ("EOT", '\EOT')
    , ("ENQ", '\ENQ')
    , ("ACK", '\ACK')
    , ("BEL", '\BEL')
    , ("BS", '\BS')
    , ("HT", '\HT')
    , ("LF", '\LF')
    , ("VT", '\VT')
    , ("FF", '\FF')
    , ("CR", '\CR')
    , ("SO", '\SO')
    , ("SI", '\SI')
    , ("DLE", '\DLE')
    , ("DC1", '\DC1')
    , ("DC2", '\DC2')
    , ("DC3", '\DC3')
    , ("DC4", '\DC4')
    , ("NAK", '\NAK')
    , ("SYN", '\SYN')
    , ("ETB", '\ETB')
    , ("CAN", '\CAN')
    , ("EM", '\EM')
    , ("SUB", '\SUB')
    , ("ESC", '\ESC')
    , ("FS", '\FS')
    , ("GS", '\GS')
    , ("RS", '\RS')
    , ("US", '\US')
    , ("SP", '\SP')
    , ("DEL", '\DEL')
    ]
