{-| This module contains the building blocks used to construct the lexer.
-}
module Agda.Syntax.Parser.LexActions
    ( -- * Main function
      lexToken
      -- * Lex actions
      -- ** General actions
    , token
    , withInterval, withInterval', withInterval_
    , withLayout
    , andThen, skip
    , begin, end, beginWith, endWith
    , begin_, end_
    , lexError
      -- ** Specialized actions
    , keyword, symbol, identifier, literal, literal', integer
      -- * Lex predicates
    , followedBy, eof, inState
    ) where

import Control.Monad.State (modify)

import Data.Bifunctor
import Data.Char
import Data.Foldable (foldl')
import Data.Maybe

import Agda.Syntax.Common (pattern Ranged)
import Agda.Syntax.Parser.Lexer
import Agda.Syntax.Parser.Alex
import Agda.Syntax.Parser.Monad
import Agda.Syntax.Parser.Tokens
import Agda.Syntax.Position
import Agda.Syntax.Literal

import Agda.Utils.List
import Agda.Utils.List1 (String1, toList)
import qualified Agda.Utils.List1 as List1

import Agda.Utils.Impossible

{--------------------------------------------------------------------------
    Scan functions
 --------------------------------------------------------------------------}

-- | Called at the end of a file. Returns 'TokEOF'.
returnEOF :: AlexInput -> Parser Token
returnEOF AlexInput{ lexSrcFile, lexPos } = do
  -- Andreas, 2018-12-30, issue #3480
  -- The following setLastPos leads to parse error reporting
  -- far away from the interesting position, in particular
  -- if there is a long comment before the EOF.
  -- (Such a long comment is frequent in interactive programming, as
  -- commenting out until the end of the file is a common habit.)
  -- -- setLastPos lexPos
  -- Without it, we get much more useful error locations.
  setPrevToken "<EOF>"
  return $ TokEOF $ posToInterval lexSrcFile lexPos lexPos

-- | Set the current input and lex a new token (calls 'lexToken').
skipTo :: AlexInput -> Parser Token
skipTo inp = do
  setLexInput inp
  lexToken

{-| Scan the input to find the next token. Calls
'Agda.Syntax.Parser.Lexer.alexScanUser'. This is the main lexing function
where all the work happens. The function 'Agda.Syntax.Parser.Lexer.lexer',
used by the parser is the continuation version of this function.
-}
lexToken :: Parser Token
lexToken =
    do  inp <- getLexInput
        lss <- getLexState
        flags <- getParseFlags
        case alexScanUser (lss, flags) inp (headWithDefault __IMPOSSIBLE__ lss) of
            AlexEOF                     -> returnEOF inp
            AlexSkip inp' len           -> skipTo inp'
            AlexToken inp' len action   -> postToken <$> runLexAction action inp inp' len
            AlexError i                 -> parseError $ concat
              [ "Lexical error"
              , case listToMaybe $ lexInput i of
                  Just '\t'                -> " (you may want to replace tabs with spaces)"
                  Just c | not (isPrint c) -> " (unprintable character)"
                  _ -> ""
              , ":"
              ]

isSub :: Char -> Bool
isSub c = '\x2080' <= c && c <= '\x2089'

readSubscript :: [Char] -> Integer
readSubscript = read . map (\c -> toEnum (fromEnum c - 0x2080 + fromEnum '0'))

postToken :: Token -> Token
postToken (TokId (r, "\x03bb")) = TokSymbol SymLambda r
postToken (TokId (r, "\x2026")) = TokSymbol SymEllipsis r
postToken (TokId (r, "\x2192")) = TokSymbol SymArrow r
postToken (TokId (r, "\x2983")) = TokSymbol SymDoubleOpenBrace r
postToken (TokId (r, "\x2984")) = TokSymbol SymDoubleCloseBrace r
postToken (TokId (r, "\x2987")) = TokSymbol SymOpenIdiomBracket r
postToken (TokId (r, "\x2988")) = TokSymbol SymCloseIdiomBracket r
postToken (TokId (r, "\x2987\x2988")) = TokSymbol SymEmptyIdiomBracket r
postToken (TokId (r, "\x2200")) = TokKeyword KwForall r
postToken t = t

{--------------------------------------------------------------------------
    Lex actions
 --------------------------------------------------------------------------}

-- | The most general way of parsing a token.
token :: (String -> Parser tok) -> LexAction tok
token action = LexAction $ \ inp inp' len ->
    do  setLexInput inp'
        let t = take len $ lexInput inp
        setPrevToken t
        setLastPos $ lexPos inp
        action t

-- | Parse a token from an 'Interval' and the lexed string.
withInterval :: ((Interval, String) -> tok) -> LexAction tok
withInterval f = token $ \s -> do
                   r <- getParseInterval
                   return $ f (r,s)

-- | Like 'withInterval', but applies a function to the string.
withInterval' :: (String -> a) -> ((Interval, a) -> tok) -> LexAction tok
withInterval' f t = withInterval (t . second f)

-- | Return a token without looking at the lexed string.
withInterval_ :: (Interval -> r) -> LexAction r
withInterval_ f = withInterval (f . fst)


-- | Executed for layout keywords. Enters the 'Agda.Syntax.Parser.Lexer.layout'
--   state and performs the given action.
withLayout :: Keyword -> LexAction r -> LexAction r
withLayout kw a = pushLexState layout `andThen` setLayoutKw `andThen` a
  where
  setLayoutKw = modify $ \ st -> st { parseLayKw = kw }

infixr 1 `andThen`

-- | Prepend some parser manipulation to an action.
andThen :: Parser () -> LexAction r -> LexAction r
andThen cmd a = LexAction $ \ inp inp' n -> do
  cmd
  runLexAction a inp inp' n

-- | Visit the current lexeme again.
revisit :: LexAction Token
revisit = LexAction $ \ _ _ _ -> lexToken

-- | Throw away the current lexeme.
skip :: LexAction Token
skip = LexAction $ \ _ inp' _ -> skipTo inp'

-- | Enter a new state without consuming any input.
begin :: LexState -> LexAction Token
begin code = beginWith code revisit

-- | Exit the current state without consuming any input.
end :: LexAction Token
end = endWith revisit

-- | Enter a new state throwing away the current lexeme.
begin_ :: LexState -> LexAction Token
begin_ code = beginWith code skip

-- | Exit the current state throwing away the current lexeme.
end_ :: LexAction Token
end_ = endWith skip

-- | Enter a new state and perform the given action.
beginWith :: LexState -> LexAction a -> LexAction a
beginWith code a = pushLexState code `andThen` a

-- | Exit the current state and perform the given action.
endWith :: LexAction a -> LexAction a
endWith a = popLexState `andThen` a


-- | Parse a 'Keyword' token, triggers layout for 'layoutKeywords'.
keyword :: Keyword -> LexAction Token
keyword k =
    case k of

        -- Unconditional layout keyword.
        _ | k `elem` layoutKeywords ->
            withLayout k cont

        -- Andreas, 2021-05-06, issue #5356:
        -- @constructor@ is not a layout keyword after all, replaced by @data _ where@.
        -- -- @constructor@ is not a layout keyword in @record ... where@ blocks,
        -- -- only in @interleaved mutual@ blocks.
        -- KwConstructor -> do
        --     cxt <- getContext
        --     if inMutualAndNotInWhereBlock cxt
        --       then withLayout k cont
        --       else cont

        _ -> cont
    where
    cont = withInterval_ (TokKeyword k)

    -- Andreas, 2021-05-06, issue #5356:
    -- @constructor@ is not a layout keyword after all, replaced by @data _ where@.
    -- -- Most recent block decides ...
    -- inMutualAndNotInWhereBlock = \case
    --   Layout KwMutual _ _ : _ -> True
    --   Layout KwWhere  _ _ : _ -> False
    --   _ : bs                  -> inMutualAndNotInWhereBlock bs
    --   []                      -> True  -- For better errors on stray @constructor@ decls.


-- | Parse a 'Symbol' token.
symbol :: Symbol -> LexAction Token
symbol s = withInterval_ (TokSymbol s)


-- | Parse a number.

number :: String -> Integer
number str = case str of
    '0' : 'x' : num -> parseNumber 16 num
    '0' : 'b' : num -> parseNumber 2  num
    num             -> parseNumber 10 num
    where
        parseNumber :: Integer -> String -> Integer
        parseNumber radix = foldl' (addDigit radix) 0

        -- We rely on Agda.Syntax.Parser.Lexer to enforce that the digits are
        -- in the correct range (so e.g. the digit 'E' cannot appear in a
        -- binary number).
        addDigit :: Integer -> Integer -> Char -> Integer
        addDigit radix n '_' = n
        addDigit radix n c   = n * radix + fromIntegral (digitToInt c)

integer :: String -> Integer
integer = \case
  '-' : str -> - (number str)
  str       -> number str

-- | Parse a literal.
literal' :: (String -> a) -> (a -> Literal) -> LexAction Token
literal' read lit = withInterval' read $ \ (r, a) ->
  TokLiteral $ Ranged (getRange r) $ lit a

literal :: Read a => (a -> Literal) -> LexAction Token
literal = literal' read

-- | Parse an identifier. Identifiers can be qualified (see 'Name').
--   Example: @Foo.Bar.f@
identifier :: LexAction Token
identifier = qualified $ either (TokId . second toList) (TokQId . map (second toList))


-- | Parse a possibly qualified name.
qualified :: (Either (Interval, String1) [(Interval, String1)] -> a) -> LexAction a
qualified tok =
    token $ \s ->
    do  i <- getParseInterval
        case mkName i $ List1.wordsBy (== '.') s of
            []  -> lexError "lex error on .."
            [x] -> return $ tok $ Left  x
            xs  -> return $ tok $ Right xs
    where
        -- Compute the ranges for the substrings (separated by '.') of
        -- a name. Dots are included: the intervals generated for
        -- "A.B.x" correspond to "A.", "B." and "x".
        mkName :: Interval -> [String1] -> [(Interval, String1)]
        mkName _ []     = []
        mkName i [x]    = [(i, x)]
        mkName i (x:xs) = (i0, x) : mkName i1 xs
            where
                p0 = iStart i
                p1 = iEnd i
                p' = movePos (movePosByString p0 x) '.'
                i0 = Interval p0 p'
                i1 = Interval p' p1


{--------------------------------------------------------------------------
    Predicates
 --------------------------------------------------------------------------}

-- | True when the given character is the next character of the input string.
followedBy :: Char -> LexPredicate
followedBy c' _ _ _ inp =
    case lexInput inp of
        []  -> False
        c:_ -> c == c'

-- | True if we are at the end of the file.
eof :: LexPredicate
eof _ _ _ inp = null $ lexInput inp

-- | True if the given state appears somewhere on the state stack
inState :: LexState -> LexPredicate
inState s (ls, _) _ _ _ = s `elem` ls
