
module Main where

import Control.Monad
import Control.Monad.Error
import Data.Char
import Data.List

import Utils.ReadP
import Utils.List

data Raw = Name String
	 | RawApp [Raw]
	 | Paren Raw
	 | Braces Raw
	 | RawLit Int
	 | AppR Raw (Arg Raw)
	 | OpR String [Raw]
    deriving (Show, Eq)

data Exp = Op String [Exp]  -- operator application
	 | App Exp (Arg Exp)
	 | Lit Int
	 | Id String

data Hiding = Hidden | NotHidden
    deriving (Eq)

data Arg e = Arg Hiding e
    deriving (Eq)

instance Show a => Show (Arg a) where
    showsPrec p (Arg Hidden e)	  = showString "{" . shows e . showString "}"
    showsPrec p (Arg NotHidden e) = showsPrec p e

instance Show Exp where
    showsPrec p e = case e of
	Id x	    -> showString x
	Lit n	    -> shows n
	App e1 e2   -> showParen (p > 1) $
	    showsPrec 1 e1 . showString " " . showsPrec 2 e2
	Op op es
	    | isPrefix op -> showParen (p > 0) $ merge ss' es'
	    | otherwise	  -> showParen (p > 0) $ merge es' ss'
	    where
		ss' = map showString $ wordsBy ('_'==) op
		es' = map (showsPrec 1) es

		isPrefix ('_':s) = False
		isPrefix _	 = True

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
	p1 = choice [ do char '('; x <- p0; char ')'; return $ Paren x
		    , do char '{'; x <- p0; char '}'; return $ Braces x
		    , RawLit . read <$> many1 (satisfy isDigit)
		    , Name <$> ((:) <$> satisfy idStart <*> many (satisfy idChar))
		    ]
	idChar  c = not $ isSpace c || elem c "(){}"
	idStart c = idChar c && not (isDigit c)

infixl 8 <$>, <*>
f <$> m = liftM f m
f <*> m = ap f m

-- General combinators
recursive :: (ReadP tok a -> [ReadP tok a -> ReadP tok a]) -> ReadP tok a
recursive f = p0
    where
	fs = f p0
	p0 = case fs of
		[]  -> pfail
		_   -> foldr ( $ ) p0 fs

-- Specific combinators
name :: String -> P String
name s = unName <$> char (Name s)
    where
	unName (Name s) = s

binop :: P Raw -> P (Raw -> Raw -> Raw)
binop opP = do
    OpR op es <- opP
    return $ \x y -> OpR ("_" ++ op ++ "_") ([x] ++ es ++ [y])

preop :: P Raw -> P (Raw -> Raw)
preop opP = do
    OpR op es <- opP
    return $ \x -> OpR (op ++ "_") (es ++ [x])

postop :: P Raw -> P (Raw -> Raw)
postop opP = do
    OpR op es <- opP
    return $ \x -> OpR ("_" ++ op) ([x] ++ es)

opP :: P Raw -> [String] -> P Raw
opP p [] = fail "empty mixfix operator"
opP p ss = OpR s <$> mix ss
    where
	s = concat $ intersperse "_" ss
	mix [s]	   = do name s; return []
	mix (s:ss) = do
	    name s
	    e <- p
	    es <- mix ss
	    return $ e : es

prefixP :: P Raw -> P Raw -> P Raw
prefixP op p = do
    fs <- many (preop op)
    e  <- p
    return $ foldr ( $ ) e fs

postfixP :: P Raw -> P Raw -> P Raw
postfixP op p = do
    e <- p
    fs <- many (postop op)
    return $ foldl (flip ( $ )) e fs

infixlP = flip chainl1 . binop
infixrP = flip chainr1 . binop
infixP opP p = do
    e1 <- p
    op <- binop opP
    e2 <- p
    return $ op e1 e2

nonfixP op p = op +++ p

appP :: P Raw -> P Raw -> P Raw
appP top p = do
    h  <- p
    es <- many (nothidden +++ hidden)
    return $ foldl AppR h es
    where
	isHidden (Braces _) = True
	isHidden _	    = False

	nothidden = Arg NotHidden <$> do
	    e <- p
	    case e of
		Braces _ -> pfail
		_	 -> return e

	hidden = do
	    Braces e <- satisfy isHidden
	    return $ Arg Hidden e

identP :: String -> P Raw
identP s = Name <$> name s

otherP :: P Raw
otherP = satisfy notName
    where
	notName (Name _) = False
	notName _	 = True

-- Running a parser
parseExp :: P Raw -> Raw -> Either String Exp
parseExp p r = case r of
    Name s	-> return $ Id s
    RawApp es	-> parseExp p =<< parseApp p es
    Paren e	-> parseExp p e
    Braces e	-> fail $ "bad hidden app"
    RawLit n	-> return $ Lit n
    AppR e1 (Arg h e2) -> do
	e1' <- parseExp p e1
	e2' <- parseExp p e2
	return $ App e1' (Arg h e2')
    OpR x es -> Op x <$> mapM (parseExp p) es

parseApp :: P Raw -> [Raw] -> Either String Raw
parseApp p es = case parse p es of
    [e]	-> return e
    []	-> fail "no parse"
    es	-> fail $ "ambiguous parse: " ++ show es

-- Tests
arithP :: P Raw
arithP = recursive $ \arithP ->
    let op = opP arithP in
    [ prefixP  $ op ["if","then"]
    , prefixP  $ op ["if","then","else"]
    , infixlP  $ op ["+"] +++ op ["-"]
    , prefixP  $ op ["-"]
    , infixlP  $ op ["*"] +++ op ["/"]
    , infixrP  $ op ["^"]
    , postfixP $ op ["!"]
    , appP arithP
    , nonfixP  $ op ["[","]"]
    , const $ otherP +++ ident
    ]
    where
	ident = choice $ map identP ["x","y","z"]

testP :: P Raw
testP = recursive $ \testP ->
    let op = opP testP in
    [ prefixP  $ op ["if","then","else"]
    , appP testP
    , const $ choice $ otherP : map identP ["x","y","Bool","False","True","false","true","tt"]
    ]

