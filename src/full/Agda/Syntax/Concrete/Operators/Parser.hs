{-# LANGUAGE CPP #-}

module Agda.Syntax.Concrete.Operators.Parser where

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Concrete.Name
import Agda.Utils.ReadP
import Agda.Utils.Monad

#include "../../../undefined.h"
import Agda.Utils.Impossible

data ExprView e
    = LocalV Name
    | OtherV e
    | AppV e (NamedArg e)
    | OpAppV Name [e]
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

----------------------------
-- Specific combinators

-- | Parse a specific identifier as a NamePart
partP :: IsExpr e => String -> ReadP e (Range, NamePart)
partP s = do
    tok <- get
    case isLocal s tok of
      Just p  -> return p
      Nothing -> pfail
    where
	isLocal x e = case exprView e of
	    LocalV (Name r [Id y]) | x == y -> Just (r, Id y)
	    _			            -> Nothing

binop :: IsExpr e => ReadP e (NewNotation,[e]) -> ReadP e (e -> e -> e)
binop middleP = do
  (nsyn,es) <- middleP
  return $ \x y -> rebuild nsyn (x : es ++ [y])

preop, postop :: IsExpr e => ReadP e (NewNotation,[e]) -> ReadP e (e -> e)
preop middleP = do
  (nsyn,es) <- middleP
  return $ \x -> rebuild nsyn (es ++ [x])

postop middleP = do
  (nsyn,es) <- middleP
  return $ \x -> rebuild nsyn (x : es)

removeExternalHoles = reverse . removeLeadingHoles . reverse . removeLeadingHoles
  where removeLeadingHoles = dropWhile isAHole


-- | Parse the "operator part" of the given syntax.
-- holes at beginning and end are IGNORED.

-- Note: it would be better to take the decision of "postprocessing" at the same
-- place as where the holes are discarded, however that would require a dependently
-- typed function (or duplicated code)
opP :: IsExpr e => ReadP e e -> NewNotation -> ReadP e (NewNotation, [e])
opP p nsyn@(_,_,syn) = do
  (range,es) <- opP' $ removeExternalHoles syn
  return (nsyn,es)
 where opP' [IdPart x] = do (r, part) <- partP x; return (r,[])
       opP' (IdPart x : _ : xs) = do
            (r1, part)    <- partP x
	    e             <- p
	    (r2 , es) <- opP' xs
            return (fuseRanges r1 r2, e : es)
       opP' x = error $ "opP': " ++ show (removeExternalHoles syn)

-- | Given a name with a syntax spec, and a list of parsed expressions
-- fitting it, rebuild the expression
rebuild :: IsExpr e => NewNotation -> [e] -> e
rebuild (name,_,syn) es = unExprView $ OpAppV name (map findExprFor [0..length es - 1])
  where filledHoles = zip es (filter isAHole syn)
        findExprFor n = case  [ e | (e,hole) <- filledHoles, holeTarget hole == Just n] of
                          [] -> error $ "no expression for hole " ++ show n
                          [x] -> x
                          _ -> error $ "more than one expression for hole " ++ show n

-- | Parse using the appropriate fixity, given a parser parsing the
-- operator part, the name of the operator, and a parser of
-- subexpressions.
infixP, infixrP, infixlP, postfixP, prefixP,nonfixP :: IsExpr e => ReadP e (NewNotation,[e]) -> ReadP e e -> ReadP e e
prefixP op p = do
    fs <- many (preop op)
    e  <- p
    return $ foldr ( $ ) e fs

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

nonfixP op p = (do
  (nsyn,es) <- op
  return (rebuild nsyn es))
 +++ p

appP :: IsExpr e => ReadP e e -> ReadP e e -> ReadP e e
appP top p = do
    h  <- p
    es <- many (nothidden +++ hidden)
    return $ foldl app h es
    where

	app e arg = unExprView $ AppV e arg

	isHidden (HiddenArgV _) = True
	isHidden _	       = False

	nothidden = Arg NotHidden Relevant . unnamed <$> do
	    e <- p
	    case exprView e of
		HiddenArgV _ -> pfail
		_	     -> return e

	hidden = do
	    HiddenArgV e <- exprView <$> satisfy (isHidden . exprView)
	    return $ Arg Hidden Relevant e

atomP :: IsExpr e => (Name -> Bool) -> ReadP e e
atomP p = do
    e <- get
    case exprView e of
	LocalV x | not (p x) -> pfail
	_		     -> return e

