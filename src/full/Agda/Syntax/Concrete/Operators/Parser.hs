{-# OPTIONS -cpp #-}

module Agda.Syntax.Concrete.Operators.Parser where

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Concrete.Name
import Agda.Utils.ReadP
import Agda.Utils.Monad

#include "../../../undefined.h"
import Agda.Utils.Impossible

data ExprView e
    = LocalV Name
    | OtherV e
    | AppV e (NamedArg e)
    | OpAppV Range Name [e]
    | HiddenArgV (Named String e)
    | ParenV e
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
partP :: IsExpr e => String -> ReadP e NamePart
partP s = do
    tok <- get
    case isLocal s tok of
      Just p  -> return p
      Nothing -> pfail
    where
	isLocal x e = case exprView e of
	    LocalV (Name r [Id _ y]) | x == y -> Just (Id r y)
	    _			              -> Nothing

binop :: IsExpr e => ReadP e e -> ReadP e (e -> e -> e)
binop opP = do
    OpAppV r (Name r' ps) es <- exprView <$> opP
    return $ \x y -> unExprView $
      OpAppV (fuseRange x y) (Name r' ([Hole] ++ ps ++ [Hole])) ([x] ++ es ++ [y])

preop :: IsExpr e => ReadP e e -> ReadP e (e -> e)
preop opP = do
    OpAppV r (Name r' ps) es <- exprView <$> opP
    return $ \x -> unExprView $
      OpAppV (fuseRange r x) (Name r' (ps ++ [Hole])) (es ++ [x])

postop :: IsExpr e => ReadP e e -> ReadP e (e -> e)
postop opP = do
    OpAppV r (Name r' ps) es <- exprView <$> opP
    return $ \x -> unExprView $
      OpAppV (fuseRange x r) (Name r' ([Hole] ++ ps)) ([x] ++ es)

opP :: IsExpr e => ReadP e e -> Name -> ReadP e e
opP p (NoName _ _)  = pfail
opP p x@(Name r xs) = do
    (ps, es) <- mix [ x | Id _ x <- xs ]
    return $ unExprView $ OpAppV (getRange ps) (Name noRange ps) es
    where
	mix []	   = __IMPOSSIBLE__
	mix [x]	   = do part <- partP x; return ([part], [])
	mix (x:xs) = do
	    part <- partP x
	    e  <- p
	    (ps, es) <- mix xs
	    return (part : Hole : ps, e : es)

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

	nothidden = Arg NotHidden . unnamed <$> do
	    e <- p
	    case exprView e of
		HiddenArgV _ -> pfail
		_	     -> return e

	hidden = do
	    HiddenArgV e <- exprView <$> satisfy (isHidden . exprView)
	    return $ Arg Hidden e

atomP :: IsExpr e => (Name -> Bool) -> ReadP e e
atomP p = do
    e <- get
    case exprView e of
	LocalV x | not (p x) -> pfail
	_		     -> return e

