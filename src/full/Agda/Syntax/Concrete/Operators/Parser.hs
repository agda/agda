{-# LANGUAGE CPP, ScopedTypeVariables #-}

module Agda.Syntax.Concrete.Operators.Parser where

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Name
import Agda.Utils.ReadP
import Agda.Utils.Monad

#include "../../../undefined.h"
import Agda.Utils.Impossible

data ExprView e
    = LocalV QName
    | WildV e
    | OtherV e
    | AppV e (NamedArg e)
    | OpAppV QName [OpApp e]
    | HiddenArgV (Named String e)
    | InstanceArgV (Named String e)
    | LamV [LamBinding] e
    | ParenV e
--    deriving (Show)

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

-- | Variant of chainr1
chainr1' :: ReadP t a -> ReadP t (a -> a -> ReadP t a) -> ReadP t a
chainr1' p op = scan
  where scan   = p >>= rest
        rest x = do f <- op
                    y <- scan
                    f x y
                 +++ return x

-- | Variant of chainl1
chainl1' :: ReadP t a -> ReadP t (a -> a -> ReadP t a) -> ReadP t a
chainl1' p op = p >>= rest
  where rest x = do f <- op
                    y <- p
                    fxy <- f x y
                    rest fxy
                 +++ return x

----------------------------
-- Specific combinators

-- | Parse a specific identifier as a NamePart
partP :: IsExpr e => [Name] -> String -> ReadP e Range
partP ms s = do
    tok <- get
    case isLocal tok of
      Just p  -> return p
      Nothing -> pfail
    where
        str = show (foldr Qual (QName (Name noRange [Id s])) ms)
	isLocal e = case exprView e of
	    LocalV y | str == show y -> Just (getRange y)
	    _			     -> Nothing

binop :: IsExpr e => ReadP e (NewNotation,Range,[e]) -> ReadP e (e -> e -> ReadP a e)
binop middleP = do
  (nsyn,r,es) <- middleP
  return $ \x y -> rebuild nsyn r (x : es ++ [y])

preop, postop :: IsExpr e => ReadP e (NewNotation,Range,[e]) -> ReadP e (e -> ReadP a e)
preop middleP = do
  (nsyn,r,es) <- middleP
  return $ \x -> rebuild nsyn r (es ++ [x])

postop middleP = do
  (nsyn,r,es) <- middleP
  return $ \x -> rebuild nsyn r (x : es)



-- | Parse the "operator part" of the given syntax.
-- holes at beginning and end are IGNORED.

-- Note: it would be better to take the decision of "postprocessing" at the same
-- place as where the holes are discarded, however that would require a dependently
-- typed function (or duplicated code)
opP :: IsExpr e => ReadP e e -> NewNotation -> ReadP e (NewNotation,Range,[e])
opP p nsyn@(q,_,syn) = do
  (range,es) <- worker (init $ qnameParts q) $ removeExternalHoles syn
  return (nsyn,range,es)
 where worker ms [IdPart x] = do r <- partP ms x; return (r,[])
       worker ms (IdPart x : _ : xs) = do
            r1        <- partP ms x
	    e         <- p
	    (r2 , es) <- worker [] xs -- only the first part is qualified
            return (fuseRanges r1 r2, e : es)
       worker _ x = __IMPOSSIBLE__ -- holes and non-holes must be alternated.

       removeExternalHoles = reverse . removeLeadingHoles . reverse . removeLeadingHoles
           where removeLeadingHoles = dropWhile isAHole

-- | Given a name with a syntax spec, and a list of parsed expressions
-- fitting it, rebuild the expression.
-- Note that this function must not parse any input (as guaranteed by the type)
rebuild :: forall symbol e. IsExpr e => NewNotation -> Range -> [e] -> ReadP symbol e
rebuild (name,_,syn) r es = do
  exprs <- mapM findExprFor [0..lastHole]
  return $ unExprView $ OpAppV (setRange r name) exprs
  where filledHoles = zip es (filter isAHole syn)
        lastHole = maximum [t | Just t <- map holeTarget syn]
        findExprFor :: Int -> ReadP a (OpApp e)
        findExprFor n = case [e | (e,NormalHole m) <- filledHoles, m == n] of
                          [] -> fail $ "no expression for hole " ++ show n
                          [x] -> case [e | (e,BindHole m) <- filledHoles, m == n] of
                                   [] -> return (Ordinary x) -- no variable to bind
                                   vars -> do bs <- mapM rebuildBinding $ map exprView vars
                                              return $ SyntaxBindingLambda (fuseRange bs x) bs x
                          _ -> fail $ "more than one expression for hole " ++ show n

rebuildBinding :: ExprView e -> ReadP a LamBinding
  -- Andreas, 2011-04-07 put just 'Relevant' here, is this correct?
rebuildBinding (LocalV (QName name)) = return $ DomainFree defaultArgInfo $ mkBoundName_ name
rebuildBinding (WildV e) =
  return $ DomainFree defaultArgInfo $ mkBoundName_ $ Name noRange [Hole]
rebuildBinding _ = fail "variable name expected"

($$$) :: (e -> ReadP a e) -> ReadP a e -> ReadP a e
f $$$ x = do
   x' <- x
   f x'

-- | Parse using the appropriate fixity, given a parser parsing the
-- operator part, the name of the operator, and a parser of
-- subexpressions.
infixP, infixrP, infixlP, postfixP, prefixP,nonfixP :: IsExpr e => ReadP e (NewNotation,Range,[e]) -> ReadP e e -> ReadP e e
prefixP op p = do
    fs <- many (preop op)
    e  <- p
    foldr (($$$)) (return e) fs

postfixP op p = do
    e <- p
    fs <- many (postop op)
    foldl (flip ( $$$ )) (return e) fs

infixlP op p = chainl1' p (binop op)
infixrP op p = chainr1' p (binop op)
infixP  op p = do
    e <- p
    restP e
    where
	restP x = return x +++ do
	    f <- binop op
	    e <- p
	    f x e

nonfixP op p = (do
  (nsyn,r,es) <- op
  rebuild nsyn r es)
 +++ p

appP :: IsExpr e => ReadP e e -> ReadP e e -> ReadP e e
appP top p = do
    h  <- p
    es <- many (nothidden +++ hidden +++ instanceH)
    return $ foldl app h es
    where

	app e arg = unExprView $ AppV e arg

	isHidden (HiddenArgV _) = True
	isHidden _	        = False

	isInstance (InstanceArgV _) = True
	isInstance _	            = False

	nothidden = defaultArg . unnamed <$> do
	    e <- p
	    case exprView e of
		HiddenArgV   _ -> pfail
		InstanceArgV _ -> pfail
		_	       -> return e

	instanceH = do
	    InstanceArgV e <- exprView <$> satisfy (isInstance . exprView)
	    return $ makeInstance $ defaultArg e

	hidden = do
	    HiddenArgV e <- exprView <$> satisfy (isHidden . exprView)
	    return $ hide $ defaultArg e

atomP :: IsExpr e => (QName -> Bool) -> ReadP e e
atomP p = do
    e <- get
    case exprView e of
	LocalV x | not (p x) -> pfail
	_		     -> return e
