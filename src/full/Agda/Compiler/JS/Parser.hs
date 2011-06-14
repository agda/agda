module Agda.Compiler.JS.Parser where

-- This is a simple parser for the ECMAScript FFI, which parses a
-- subset of ECMAscript expressions. We do this so that we can
-- optimize code that contains FFI expressions, for example
-- {-# COMPILED_JS _+_ function (x) { return function (y) { return x+y; }; } #-}
-- will generate ECMAScript "1 + 2" from Agda "1 + 2".

import Prelude hiding ( exp, lookup )
import Control.Monad.Identity ( Identity )
import Data.List ( genericLength )
import Data.Char ( isSpace, isLetter, isAlphaNum, isDigit )
import Data.Map ( Map, fromList, union, empty )
import qualified Data.Map as M
import qualified Data.Map as M

import Agda.Utils.ReadP
  ( ReadP, (+++), (<++), between, chainl1, char, choice, look, many, many1,
    munch, munch1, parse', pfail, satisfy, sepBy, string, skipSpaces )

import Agda.Syntax.Common ( Nat )
import Agda.Compiler.JS.Syntax
  ( LocalId(LocalId), GlobalId(GlobalId), MemberId(MemberId),
    Exp(Self,Local,Global,Undefined,String,Integer,Lambda,Apply,Object,Lookup,If,BinOp,PreOp,Const) )

type Parser = ReadP Char

identifier :: Parser String
identifier = do
  c <- satisfy isLetter
  cs <- munch isAlphaNum
  skipSpaces
  return (c : cs)

wordBoundary :: Parser ()
wordBoundary = do
  cs <- look
  case cs of
    (c:_) | isAlphaNum c -> pfail
    _                    -> return ()

token :: String -> Parser ()
token s = string s >> wordBoundary >> skipSpaces

punct :: Char -> Parser ()
punct c = char c >> skipSpaces

parened :: Parser a -> Parser a
parened = between (punct '(')  (punct ')')

braced :: Parser a -> Parser a
braced = between (punct '{')  (punct '}')

bracketed :: Parser a -> Parser a
bracketed = between (punct '[')  (punct ']')

quoted :: Parser a -> Parser a
quoted = between (char '"') (punct '"')

stringLit :: Parser Exp
stringLit = do s <- stringStr; return (String s)

stringStr :: Parser String
stringStr = quoted (many stringChr)

stringChr :: Parser Char
stringChr = satisfy (`notElem` "\\\"") +++ escChr

-- Not handling all escape sequences
escChr :: Parser Char
escChr = char '\\' >> (
  (char 'n' >> return '\n') +++
  (char 'r' >> return '\r') +++
  (char 't' >> return '\t') +++
  (char '"' >> return '"') +++
  (char '\\' >> return '\\')
 )

-- Not handling all integer constants
intLit :: Parser Exp
intLit = do s <- munch1 isDigit; skipSpaces; return (Integer (read s))

undef :: Parser Exp
undef = token "undefined" >> return Undefined

localid :: (Map String Nat) -> Parser Exp
localid m = do
  s <- identifier
  case M.lookup s m of
    Nothing -> return (Const s)
    Just i -> return (Local (LocalId i))

globalid :: Parser Exp
globalid = do
  token "require"
  i <- parened (quoted (sepBy (munch1 isAlphaNum) (char '.')))
  return (Global (GlobalId i))

preop :: Parser String
preop = do
  op <- choice (map string [ "+", "-", "!" ])
  skipSpaces
  return op

binop :: Parser String
binop = do
  op <- choice (map string [
      "<", ">", "<=", ">=", "==", "===", "<<", ">>",
      "<<<", ">>>", "!=", "!==", "+", "-", "*", "%", "/",
      "&", "&&", "|", "||", "^"
    ])
  skipSpaces
  return op

field :: (Map String Nat) -> Parser (MemberId,Exp)
field m = do
  l <- stringStr
  punct ':'
  e <- exp m
  return (MemberId l, e)

object :: (Map String Nat) -> Parser Exp
object m = do
  o <- braced (sepBy (field m) (punct ','))
  return (Object (fromList o))

function :: (Map String Nat) -> Parser Exp
function m = do
  token "function"
  xs <- parened (sepBy identifier (punct ','))
  n <- return (genericLength xs)
  m' <- return (union (fromList (zip xs [n-1,n-2..0])) (M.map (+n) m))
  e <- bracedBlock m'
  return (Lambda n e)

bracedBlock :: (Map String Nat) -> Parser Exp
bracedBlock m = braced (returnBlock m +++ ifBlock m +++ bracedBlock m)

returnBlock :: (Map String Nat) -> Parser Exp
returnBlock m = between (token "return") (punct ';') (exp m)

ifBlock :: (Map String Nat) -> Parser Exp
ifBlock m = do
  token "if"
  e <- parened (exp m)
  f <- bracedBlock m
  token "else"
  g <- (ifBlock m +++ bracedBlock m)
  return (If e f g)

exp0 :: (Map String Nat) -> Parser Exp
exp0 m = function m <++ undef <++ globalid <++ localid m <++
         object m <++ stringLit <++ intLit <++ parened (exp m)

exp1 :: (Map String Nat) -> Parser Exp
exp1 m =
  (do op <- preop; e <- exp1 m; return (PreOp op e)) <++
  (exp0 m)

exp2 :: (Map String Nat) -> Parser Exp
exp2 m = exp1 m >>= exp2' m

-- Not handling operator fixity or precedence
exp2' :: (Map String Nat) -> Exp -> Parser Exp
exp2' m e =
  (do es <- parened (sepBy (exp m) (punct ',')); exp2' m (Apply e es)) <++
  (do i <- bracketed stringStr; exp2' m (Lookup e (MemberId i))) <++
  (do punct '.'; i <- identifier; exp2' m (Lookup e (MemberId i))) <++
  (do op <- binop; f <- exp0 m; exp2' m (BinOp e op f)) <++
  (return e)

exp3 :: (Map String Nat) -> Parser Exp
exp3 m = exp2 m >>= exp3' m

exp3' :: (Map String Nat) -> Exp -> Parser Exp
exp3' m e =
  (do punct '?'; f <- exp2 m; punct ':'; g <- exp2 m; return (If e f g)) <++
  (return e)

exp :: (Map String Nat) -> Parser Exp
exp = exp3

topLevel :: Parser Exp
topLevel = skipSpaces >> exp empty

parse :: String -> Either Exp String
parse = parse' topLevel
