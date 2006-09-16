{-# OPTIONS -cpp #-}

module Syntax.Concrete.Operators.Parser where

import Syntax.Position
import Syntax.Common
import Syntax.Concrete
import Syntax.Fixity
import Utils.ReadP
import Utils.Monad

#include "../../../undefined.h"

---------------------------------------------------------------------------
-- * Parser combinators
---------------------------------------------------------------------------

type OpP = ReadP Expr

-- | Combining a hierarchy of parsers.
recursive :: (ReadP tok a -> [ReadP tok a -> ReadP tok a]) -> ReadP tok a
recursive f = p0
    where
	fs = f p0
	p0 = foldr ( $ ) p0 fs

-- Specific combinators
nameP :: Name -> OpP Name
nameP x = do
    Ident (QName x) <- char (Ident $ QName x)
    return x

binop :: OpP Expr -> OpP (Expr -> Expr -> Expr)
binop opP = do
    OpApp r op es <- opP
    return $ \x y -> OpApp r op ([x] ++ es ++ [y])

preop :: OpP Expr -> OpP (Expr -> Expr)
preop opP = do
    OpApp r op es <- opP
    return $ \x -> OpApp r op (es ++ [x])

postop :: OpP Expr -> OpP (Expr -> Expr)
postop opP = do
    OpApp r op es <- opP
    return $ \x -> OpApp r op ([x] ++ es)

opP :: OpP Expr -> Operator -> OpP Expr
opP p (Operator d@(NameDecl xs) _) = do
    es <- mix xs'
    return $ OpApp (getRange es) d es
    where
	xs'  = filter (/= noName) xs

	mix []	   = __IMPOSSIBLE__
	mix [x]	   = do nameP x; return []
	mix (x:xs) = do
	    nameP x
	    e  <- p
	    es <- mix xs
	    return $ e : es

prefixP :: OpP Expr -> OpP Expr -> OpP Expr
prefixP op p = do
    fs <- many1 (preop op)
    e  <- p
    return $ foldr ( $ ) e fs

postfixP :: OpP Expr -> OpP Expr -> OpP Expr
postfixP op p = do
    e <- p
    fs <- many1 (postop op)
    return $ foldl (flip ( $ )) e fs

infixP, infixrP, infixlP :: OpP Expr -> OpP Expr -> OpP Expr
infixlP op p = do
    e  <- chainl1 p (binop op)
    f  <- binop op
    e' <- p
    return $ f e e'

infixrP op p = do
    e  <- p
    f  <- binop op
    e' <- chainr1 p (binop op)
    return $ f e e'

infixP op p = do
    e1 <- p
    op <- binop op
    e2 <- p
    return $ op e1 e2

nonfixP :: OpP Expr -> OpP Expr -> OpP Expr
nonfixP op p = op +++ p

appP :: OpP Expr -> OpP Expr -> OpP Expr
appP top p = do
    h  <- p
    es <- many (nothidden +++ hidden)
    return $ foldl app h es
    where

	app e arg = App (fuseRange e arg) e arg

	isHidden (HiddenArg _ _) = True
	isHidden _		 = False

	nothidden = Arg NotHidden <$> do
	    e <- p
	    case e of
		HiddenArg _ _ -> pfail
		_	      -> return e

	hidden = do
	    HiddenArg _ e <- satisfy isHidden
	    return $ Arg Hidden e

identP :: Name -> OpP Expr
identP x = char (Ident $ QName x)

otherP :: OpP Expr
otherP = satisfy notLocalName
    where
	notLocalName (Ident (QName _)) = False
	notLocalName _		       = True


