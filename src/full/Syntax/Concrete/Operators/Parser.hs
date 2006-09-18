{-# OPTIONS -cpp #-}

module Syntax.Concrete.Operators.Parser where

import Syntax.Position
import Syntax.Common
import Syntax.Fixity
import Syntax.Concrete.Name
import Utils.ReadP
import Utils.Monad

#include "../../../undefined.h"

data ExprView e
    = LocalV Name
    | OtherV e
    | AppV e (Arg e)
    | OpAppV Range NameDecl [e]
    | HiddenArgV e
    deriving (Show)

class HasRange e => IsExpr e where
    exprView   :: e -> ExprView e
    unExprView :: ExprView e -> e

---------------------------------------------------------------------------
-- * Parser combinators
---------------------------------------------------------------------------

-- | Combining a hierarchy of parsers.
recursive :: (ReadP tok a -> [ReadP tok a -> ReadP tok a]) -> ReadP tok a
recursive f = p0
    where
	fs = f p0
	p0 = foldr ( $ ) p0 fs

-- Specific combinators
nameP :: IsExpr e => Name -> ReadP e Name
nameP x = do
    LocalV x <- exprView <$> satisfy (isLocal x)
    return x
    where
	isLocal x e = case exprView e of
	    LocalV y -> x == y
	    _	    -> False

binop :: IsExpr e => ReadP e e -> ReadP e (e -> e -> e)
binop opP = do
    OpAppV r op es <- exprView <$> opP
    return $ \x y -> unExprView $ OpAppV r op ([x] ++ es ++ [y])

preop :: IsExpr e => ReadP e e -> ReadP e (e -> e)
preop opP = do
    OpAppV r op es <- exprView <$> opP
    return $ \x -> unExprView $ OpAppV r op (es ++ [x])

postop :: IsExpr e => ReadP e e -> ReadP e (e -> e)
postop opP = do
    OpAppV r op es <- exprView <$> opP
    return $ \x -> unExprView $ OpAppV r op ([x] ++ es)

opP :: IsExpr e => ReadP e e -> Operator -> ReadP e e
opP p (Operator d@(NameDecl xs) _) = do
    es <- mix xs'
    return $ unExprView $ OpAppV (getRange es) d es
    where
	xs'  = filter (/= noName) xs

	mix []	   = __IMPOSSIBLE__
	mix [x]	   = do nameP x; return []
	mix (x:xs) = do
	    nameP x
	    e  <- p
	    es <- mix xs
	    return $ e : es

prefixP :: IsExpr e => ReadP e e -> ReadP e e -> ReadP e e
prefixP op p = do
    fs <- many (preop op)
    e  <- p
    return $ foldr ( $ ) e fs

postfixP :: IsExpr e => ReadP e e -> ReadP e e -> ReadP e e
postfixP op p = do
    e <- p
    fs <- many (postop op)
    return $ foldl (flip ( $ )) e fs

infixP, infixrP, infixlP :: IsExpr e => ReadP e e -> ReadP e e -> ReadP e e
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

nonfixP :: IsExpr e => ReadP e e -> ReadP e e -> ReadP e e
nonfixP op p = op +++ p

appP :: IsExpr e => ReadP e e -> ReadP e e -> ReadP e e
appP top p = do
    h  <- p
    es <- many (nothidden +++ hidden)
    return $ foldl app h es
    where

	app e arg = unExprView $ AppV e arg

	isHidden (HiddenArgV _) = True
	isHidden _	       = False

	nothidden = Arg NotHidden <$> do
	    e <- p
	    case exprView e of
		HiddenArgV _ -> pfail
		_	    -> return e

	hidden = do
	    HiddenArgV e <- exprView <$> satisfy (isHidden . exprView)
	    return $ Arg Hidden e

atomP :: IsExpr e => (Name -> Bool) -> ReadP e e
atomP p = do
    e <- get
    case exprView e of
	LocalV x | not (p x) -> pfail
	_		     -> return e

