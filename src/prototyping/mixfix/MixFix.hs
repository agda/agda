
module Main where

import Control.Monad
import Control.Monad.Error
import Data.Char
import Data.List
import qualified Data.Set as Set

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
type Parser = P Raw

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
	p0 = foldr ( $ ) p0 fs
	choice' = foldr1 (++++)
	f ++++ g = \p -> f p +++ g p

-- Specific combinators
name :: String -> P String
name s = unName <$> char (Name s)
    where
	unName (Name s) = s

binop :: Parser -> P (Raw -> Raw -> Raw)
binop opP = do
    OpR op es <- opP
    return $ \x y -> OpR ("_" ++ op ++ "_") ([x] ++ es ++ [y])

preop :: Parser -> P (Raw -> Raw)
preop opP = do
    OpR op es <- opP
    return $ \x -> OpR (op ++ "_") (es ++ [x])

postop :: Parser -> P (Raw -> Raw)
postop opP = do
    OpR op es <- opP
    return $ \x -> OpR ("_" ++ op) ([x] ++ es)

opP :: Parser -> [String] -> Parser
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

prefixP :: Parser -> Parser -> Parser
prefixP op p = do
    fs <- many (preop op)
    e  <- p
    return $ foldr ( $ ) e fs

postfixP :: Parser -> Parser -> Parser
postfixP op p = do
    e <- p
    fs <- many (postop op)
    return $ foldl (flip ( $ )) e fs

infixlP op p = chainl1 p (binop op)
infixrP op p = chainr1 p (binop op)
infixP  op p = do
    e <- p
    f <- restP
    return $ f e
    where
	restP = return id +++ do
	    f <- binop op
	    e <- p
	    return $ flip f e

nonfixP op p = op +++ p

appP :: Parser -> Parser
appP p = do
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

atomP :: [String] -> Parser
atomP xs = do
    t <- get
    case t of
	Name x | not $ Set.member x xs'
	    -> pfail
	_   -> return t
    where
	xs' = Set.fromList xs

-- Running a parser
parseExp :: Parser -> Raw -> Either String Exp
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

parseApp :: Parser -> [Raw] -> Either String Raw
parseApp p es = case parse p es of
    [e]	-> return e
    []	-> fail "no parse"
    es	-> fail $ "ambiguous parse: " ++ show es

-- Building the parser
data Operator = Prefix  { opPrecedence :: Int, opName :: [String] }
	      | Postfix { opPrecedence :: Int, opName :: [String] }
	      | InfixL  { opPrecedence :: Int, opName :: [String] }
	      | InfixR  { opPrecedence :: Int, opName :: [String] }
	      | Infix   { opPrecedence :: Int, opName :: [String] }
	      | Nonfix  { opName :: [String] }
    deriving Show

buildParser :: [String] -> [Operator] -> Parser
buildParser local ops =
    recursive $ \p ->
	let op = opP p in
	map (mkP op) (order fixops)
	++ [ appP ]
	++ map (nonfixP . op . opName) nonops
	++ [ const $ atomP local ]
    where

	(nonops, fixops) = partition nonfix ops

	isprefix (Prefix _ _)	= True
	isprefix _		= False

	ispostfix (Postfix _ _) = True
	ispostfix _		= False

	isinfixl (InfixL _ _)	= True
	isinfixl _		= False

	isinfixr (InfixR _ _)	= True
	isinfixr _		= False

	isinfix (Infix _ _)	= True
	isinfix _		= False

	nonfix (Nonfix _)	= True
	nonfix _		= False

	on f g x y = f (g x) (g y)

	order = groupBy ((==) `on` opPrecedence) . sortBy (compare `on` opPrecedence)

	mkP op ops = case concat [infx, inlfx, inrfx, prefx, postfx] of
		[]	-> id
		[(_,f)] -> f
		xs	-> error $ "cannot mix " ++ show (map fst xs)
	    where
		choice' = foldr1 (++++)
		f ++++ g = \p -> f p +++ g p
		inlfx	= fixP infixlP  isinfixl
		inrfx	= fixP infixrP  isinfixr
		infx	= fixP infixP   isinfix
		prefx	= fixP prefixP  isprefix
		postfx	= fixP postfixP ispostfix

		fixP f g = case filter g ops of
			    []	-> []
			    os	-> [ (os, f $ choice $ map (op . opName) os) ]

-- Tests
arithP :: Parser
arithP = buildParser xs ops
    where
	xs = map (:[]) ['a'..'z']
	ops =
	    [ InfixL  20 ["+"]
	    , InfixL  30 ["*"]
	    , InfixR  40 ["^"]
	    , Postfix 35 ["!"]
	    , InfixR  15 [":"]
	    , InfixR  18 ["/\\"]
	    , InfixR  16 ["\\/"]
	    ]

testP :: Parser
testP = buildParser xs ops
    where
	xs = map (:[]) ['a'..'z']
	ops = [ InfixL n ["+" ++ show n] | n <- [0..20] ]

arithP' :: Parser
arithP' = recursive $ \p ->
    let op = opP p in
    [ id ++++ infixrP (op [":"])
    , id ++++ infixrP (op ["\\/"])
    , id ++++ infixrP (op ["/\\"])
    , id ++++ infixlP (op ["+"])
    , id ++++ infixlP (op ["*"])
    , id ++++ postfixP (op ["!"])
    , id ++++ infixrP (op ["^"])
    , appP
    , const $ atomP $ map (:[]) ['a'..'z']
    ]
    where
	f ++++ g = \p -> f p +++ g p

main = print $ parseExp testP $ parseRaw "1 +0 2 +0 3"
