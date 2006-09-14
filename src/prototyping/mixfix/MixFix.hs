
module Main where

import Control.Monad
import Control.Monad.Error
import Data.Char
import Data.List

import ReadP

data Raw = Name String
	 | RawApp [Raw]
	 | Paren Raw
	 | RawLit Int
    deriving (Show, Eq)

data Exp = Op [String] [Exp]  -- operator application
	 | App Exp Exp
	 | Lit Int
	 | Id String

instance Show Exp where
    showsPrec p e = case e of
	Id x	    -> showString x
	Lit n	    -> shows n
	App e1 e2   -> showParen (p > 1) $
	    showsPrec 1 e1 . showString " " . showsPrec 2 e2
	Op ss es
	    | n == m -> showParen (p > 0) $ merge ss' es'
	    | n < m  -> showParen (p > 0) $ merge es' ss'
	    | n > m  -> merge ss' es'
	    where
		n = length ss
		m = length es
		ss' = map showString ss
		es' = map (showsPrec 1) es

		merge xs ys = foldr (.) id $ intersperse (showString " ") $ merge' xs ys

		merge' (x:xs) (y:ys) = x : y : merge' xs ys
		merge' []      ys    = ys
		merge' xs      []    = xs

type P = ReadP Raw

-- Parsing raw terms (for testing)
parseRaw :: String -> Raw
parseRaw s = case parse p0 s of
    [e]	-> e
    []	-> error "parseRaw: no parse"
    es	-> error $ "parseRaw: ambiguous parse: " ++ show es
    where
	p0 = RawApp <$> sepBy1 p1 (many1 $ satisfy isSpace)
	p1 = choice [ do char '('; x <- p0; char ')'; return x
		    , RawLit . read <$> many1 (satisfy isDigit)
		    , Name <$> ((:) <$> satisfy idStart <*> many (satisfy idChar))
		    ]
	idChar  c = not $ isSpace c || elem c "()"
	idStart c = idChar c && not (isDigit c)

infixl 8 <$>, <*>
f <$> m = liftM f m
f <*> m = ap f m

-- General combinators
recursive :: [ReadP tok a -> ReadP tok a] -> ReadP tok a
recursive [] = pfail
recursive fs = p0
    where
	p0 = foldr ( $ ) p0 fs

-- Specific combinators
name :: String -> P String
name s = unName <$> char (Name s)
    where
	unName (Name s) = s

binop :: P Exp -> P (Exp -> Exp -> Exp)
binop opP = do
    Op op es <- opP
    return $ \x y -> Op op ([x] ++ es ++ [y])

preop :: P Exp -> P (Exp -> Exp)
preop opP = do
    Op op es <- opP
    return $ \x -> Op op (es ++ [x])

postop :: P Exp -> P (Exp -> Exp)
postop opP = do
    Op op es <- opP
    return $ \x -> Op op ([x] ++ es)

opP :: P Exp -> [String] -> P Exp
opP p [] = fail "empty mixfix operator"
opP p ss = Op ss <$> mix ss
    where
	mix [s]	   = do name s; return []
	mix (s:ss) = do
	    name s
	    e <- p
	    es <- mix ss
	    return $ e : es

prefixP :: P Exp -> P Exp -> P Exp
prefixP op p = do
    fs <- many (preop op)
    e  <- p
    return $ foldr ( $ ) e fs

postfixP :: P Exp -> P Exp -> P Exp
postfixP op p = do
    e <- p
    fs <- many (postop op)
    return $ foldl (flip ( $ )) e fs

infixlP = flip chainl1 . binop
infixrP = flip chainr1 . binop
infixP opP p = do
    e1 <- binop p
    op <- opP
    e2 <- binop p
    return $ op e1 e2

nonfixP op p = op +++ p

appP :: P Exp -> P Exp
appP p = chainl1 p (return App)

identP :: String -> P Exp
identP s = Id <$> name s

otherP :: P Exp -> P Exp
otherP p = do
    r <- satisfy notName
    case parseExp p r of
	Right e  -> return e
	Left err -> fail err
    where
	notName (Name _) = False
	notName _	 = True

-- Running a parser
parseExp :: P Exp -> Raw -> Either String Exp
parseExp p r = case r of
    Name s	-> parseApp p [Name s]
    RawApp es	-> parseApp p es
    Paren e	-> parseExp p e
    RawLit n	-> return $ Lit n

parseApp :: P Exp -> [Raw] -> Either String Exp
parseApp p es = case parse p es of
    [e]	-> return e
    []	-> fail "no parse"
    es	-> fail $ "ambiguous parse: " ++ show es

-- Tests
arithP :: P Exp
arithP = recursive
    [ prefixP  $ op ["if","then"]
    , prefixP  $ op ["if","then","else"]
    , infixlP  $ op ["+"] +++ op ["-"]
    , prefixP  $ op ["-"]
    , infixlP  $ op ["*"] +++ op ["/"]
    , postfixP $ op ["!"]
    , appP
    , nonfixP  $ op ["[","]"]
    , \p -> otherP p +++ ident
    ]
    where
	op = opP arithP
	ident = choice $ map identP ["x","y","z"]

