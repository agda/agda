{-# OPTIONS -fglasgow-exts -cpp #-}

{-| The parser doesn't know about operators and parses everything as normal
    function application. This module contains the functions that parses the
    operators properly. For a stand-alone implementation of this see
    @src\/prototyping\/mixfix@.

    It also contains the function that puts parenthesis back given the
    precedence of the context.
-}
module Syntax.Concrete.Operators
    ( parseApplication
    , parseLHS
    , paren
    , mparen
    ) where

import Prelude hiding (putStrLn, print, putStr)
import Utils.IO

import Control.Applicative
import Control.Monad.Trans
import Data.Typeable
import Data.Traversable (traverse)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List

import Syntax.Concrete.Pretty ()
import Syntax.Common
import Syntax.Concrete
import Syntax.Concrete.Operators.Parser
import qualified Syntax.Abstract.Name as A
import Syntax.Position
import Syntax.Fixity
import Syntax.Scope.Base
import Syntax.Scope.Monad

import TypeChecking.Monad.Base (typeError, TypeError(..))
import TypeChecking.Monad.State (getScope)

import Utils.ReadP
import Utils.Monad
import Utils.Tuple
import Utils.Function

#include "../../undefined.h"

---------------------------------------------------------------------------
-- * Building the parser
---------------------------------------------------------------------------

partsInScope :: ScopeM (Set Name)
partsInScope = do
    xs <- uncurry (++) . (id -*- map fst) <$> localNames
    return $ Set.fromList $ concatMap parts xs
    where
	parts (NoName _ _)   = []
	parts x@(Name _ [_]) = [x]
	parts x@(Name _ xs ) = x : [ Name r [i] | i@(Id r _) <- xs ]

-- | Compute all unqualified defined names in scope and their fixities.
getDefinedNames :: [KindOfName] -> ScopeM [(Name, Fixity)]
getDefinedNames kinds = do
  names <- allNamesInScope . mergeScopes . scopeStack <$> getScope
  return [ (x, A.nameFixity $ A.qnameName $ anameName d)
	 | (QName x, ds) <- Map.assocs names
	 , d		 <- take 1 ds
	 , anameKind d `elem` kinds
	 ]

-- | Compute all names (first component) and operators (second component) in
--   scope.
localNames :: ScopeM ([Name], [(Name, Fixity)])
localNames = do
  defs   <- getDefinedNames [DefName, ConName]
  locals <- scopeLocals <$> getScope
  return $ split $ nubBy ((==) `on` fst) $ map localOp locals ++ defs
  where
    localOp (x, _) = (x, defaultFixity)
    split ops = ([ x | Left x <- zs], [ y | Right y <- zs ])
	where
	    zs = concatMap opOrNot ops

    opOrNot (x@(Name _ [_]), fx) = [Left x]
    opOrNot (x, fx)		 = [Left x, Right (x, fx)]

data UseBoundNames = UseBoundNames | DontUseBoundNames

{-| Builds parser for operator applications from all the operators and function
    symbols in scope. When parsing a pattern we 'DontUseBoundNames' since a
    pattern binds new variables, but when parsing an expression we
    'UseBoundNames' and refute application of things that aren't in scope. The
    reason for this is to disambiguate things like @x + y@. This could mean
    both @_+_@ applied to @x@ and @y@, and @x@ applied to @+@ and @y@, but if there
    is no @+@ in scope it could only be the first.

    To avoid problems with operators of the same precedence but different
    associativity we decide (completely arbitrary) to fix the precedences of
    operators with the same given precedence in the following order (from
    loosest to hardest):

    - non-associative

    - left associative

    - right associative

    - prefix

    - postfix

    This has the effect that if you mix operators with the same precedence but
    different associativity the parser won't complain. One could argue that
    this is a Bad Thing, but since it's not trivial to implement the check it
    will stay this way until people start complaining about it.

    TODO: Clean up (too many fst and snd)
-}
buildParser :: IsExpr e => Range -> UseBoundNames -> ScopeM (ReadP e e)
buildParser r use = do
    (names, ops) <- localNames
    cons	 <- getDefinedNames [ConName]
    let conparts   = Set.fromList $ concatMap (parts . fst) cons
	connames   = Set.fromList $ map fst cons
	(non, fix) = partition nonfix ops
	set	   = Set.fromList names
	isLocal    = case use of
	    UseBoundNames     -> \x -> Set.member x set
	    DontUseBoundNames -> \x -> Set.member x connames || not (Set.member x conparts)
    return $ recursive $ \p ->
	concatMap (mkP p) (order fix)
	++ [ appP p ]
	++ map (nonfixP . opP p . fst) non
	++ [ const $ atomP isLocal ]
    where
	parts (NoName _ _) = []
	parts (Name _ [_]) = []
	parts (Name _ xs ) = [ Name r [i] | i@(Id r _) <- xs ]

	level = fixityLevel . snd

	isinfixl (op, LeftAssoc _ _)  = isInfix op
	isinfixl _		      = False

	isinfixr (op, RightAssoc _ _) = isInfix op
	isinfixr _		      = False

	isinfix (op, NonAssoc _ _)    = isInfix op
	isinfix _		      = False

	on f g x y = f (g x) (g y)

	nonfix = isNonfix . fst
	order = groupBy ((==) `on` level) . sortBy (compare `on` level)

	mkP p0 ops = case concat [infx, inlfx, inrfx, prefx, postfx] of
	    []	    -> [id]
	    fs	    -> fs
	    where
		choice' = foldr1 (++++)
		f ++++ g = \p -> f p +++ g p
		inlfx	= fixP infixlP  isinfixl
		inrfx	= fixP infixrP  isinfixr
		infx	= fixP infixP   isinfix
		prefx	= fixP prefixP  (isPrefix . fst)
		postfx	= fixP postfixP (isPostfix . fst)

		fixP f g =
		    case filter g ops of
			[]  -> []
			ops -> [ f $ choice $ map (opP p0 . fst) ops ]

---------------------------------------------------------------------------
-- * Expression instances
---------------------------------------------------------------------------

instance IsExpr Expr where
    exprView e = case e of
	Ident (QName x)	-> LocalV x
	App _ e1 e2	-> AppV e1 e2
	OpApp r d es	-> OpAppV r d es
	HiddenArg _ e	-> HiddenArgV e
	Paren _ e	-> ParenV e
	_		-> OtherV e
    unExprView e = case e of
	LocalV x      -> Ident (QName x)
	AppV e1 e2    -> App (fuseRange e1 e2) e1 e2
	OpAppV r d es -> OpApp r d es
	HiddenArgV e  -> HiddenArg (getRange e) e
	ParenV e      -> Paren (getRange e) e
	OtherV e      -> e

instance IsExpr Pattern where
    exprView e = case e of
	IdentP (QName x) -> LocalV x
	AppP e1 e2	 -> AppV e1 e2
	OpAppP r d es	 -> OpAppV r d es
	HiddenP _ e	 -> HiddenArgV e
	ParenP _ e	 -> ParenV e
	_		 -> OtherV e
    unExprView e = case e of
	LocalV x	 -> IdentP (QName x)
	AppV e1 e2	 -> AppP e1 e2
	OpAppV r d es	 -> OpAppP r d es
	HiddenArgV e	 -> HiddenP (getRange e) e
	ParenV e	 -> ParenP (getRange e) e
	OtherV e	 -> e

---------------------------------------------------------------------------
-- * Parse functions
---------------------------------------------------------------------------

-- | Returns the list of possible parses.
parsePattern :: ReadP Pattern Pattern -> Pattern -> [Pattern]
parsePattern prs p = case p of
    AppP p (Arg h q) -> fullParen' <$> (AppP <$> parsePattern prs p <*> (Arg h <$> traverse (parsePattern prs) q))
    RawAppP _ ps     -> fullParen' <$> (parsePattern prs =<< parse prs ps)
    OpAppP r d ps    -> fullParen' . OpAppP r d <$> mapM (parsePattern prs) ps
    HiddenP _ _	     -> fail "bad hidden argument"
    AsP r x p	     -> AsP r x <$> parsePattern prs p
    DotP r e	     -> return $ DotP r e
    ParenP r p	     -> fullParen' <$> parsePattern prs p
    WildP _	     -> return p
    AbsurdP _	     -> return p
    LitP _	     -> return p
    IdentP _	     -> return p


-- | Parses a left-hand side, and makes sure that it defined the expected name.
--   TODO: check the arities of constructors. There is a possible ambiguity with
--   postfix constructors:
--	Assume _ * is a constructor. Then 'true *' can be parsed as either the
--	intended _* applied to true, or as true applied to a variable *. If we
--	check arities this problem won't appear.
parseLHS :: Maybe Name -> Pattern -> ScopeM Pattern
parseLHS top p = do
    patP <- buildParser (getRange p) DontUseBoundNames
    cons <- getNames [ConName]
    case filter (validPattern top cons) $ parsePattern patP p of
	[p] -> return p
	[]  -> typeError $ NoParseForLHS p
	ps  -> typeError $ AmbiguousParseForLHS p $ map fullParen ps
    where
	getNames kinds = map fst <$> getDefinedNames kinds

	validPattern :: Maybe Name -> [Name] -> Pattern -> Bool
	validPattern (Just top) cons p = case appView p of
	    IdentP (QName x) : ps -> x == top && all (validPat cons) ps
	    _			  -> False
	validPattern Nothing cons p = validPat cons p

	validPat :: [Name] -> Pattern -> Bool
	validPat cons p = case appView p of
	    [_]			  -> True
	    IdentP (QName x) : ps -> elem x cons && all (validPat cons) ps
	    ps			  -> all (validPat cons) ps

	appView :: Pattern -> [Pattern]
	appView p = case p of
	    AppP p (Arg _ q) -> appView p ++ [namedThing q]
	    OpAppP _ op ps   -> IdentP (QName op) : ps
	    ParenP _ p	     -> appView p
	    RawAppP _ _	     -> __IMPOSSIBLE__
	    HiddenP _ _	     -> __IMPOSSIBLE__
	    _		     -> [p]

parseApplication :: [Expr] -> ScopeM Expr
parseApplication [e] = return e
parseApplication es = do

    -- Check that all parts of the application are in scope (else it won't
    -- parse and we can just as well give a nice error).
    inScope <- partsInScope
    case [ QName x | Ident (QName x) <- es, not (Set.member x inScope) ] of
	[]  -> return ()
	xs  -> typeError $ NotInScope xs

    -- Build the parser
    p <- buildParser (getRange es) UseBoundNames

    -- Parse
    case parse p es of
	[e] -> return e
	[]  -> typeError $ NoParseForApplication es
	es' -> typeError $ AmbiguousParseForApplication es $ map fullParen es'

-- Inserting parenthesis --------------------------------------------------

fullParen :: IsExpr e => e -> e
fullParen e = case exprView $ fullParen' e of
    ParenV e	-> e
    e'		-> unExprView e'

fullParen' :: IsExpr e => e -> e
fullParen' e = case exprView e of
    LocalV _	 -> e
    OtherV _	 -> e
    HiddenArgV _ -> e
    ParenV _	 -> e
    AppV e1 (Arg h e2) -> par $ unExprView $ AppV (fullParen' e1) (Arg h e2')
	where
	    e2' = case h of
		Hidden	  -> e2
		NotHidden -> fullParen' <$> e2
    OpAppV r x es -> par $ unExprView $ OpAppV r x $ map fullParen' es
    where
	par = unExprView . ParenV

paren :: Monad m => (Name -> m Fixity) -> Expr -> m (Precedence -> Expr)
paren _   e@(App _ _ _)	       = return $ \p -> mparen (appBrackets p) e
paren f	  e@(OpApp _ op _)     = do fx <- f op; return $ \p -> mparen (opBrackets fx p) e
paren _   e@(Lam _ _ _)	       = return $ \p -> mparen (lamBrackets p) e
paren _   e@(Fun _ _ _)	       = return $ \p -> mparen (lamBrackets p) e
paren _   e@(Pi _ _)	       = return $ \p -> mparen (lamBrackets p) e
paren _   e@(Let _ _ _)	       = return $ \p -> mparen (lamBrackets p) e
paren _	  e@(Rec _ _)	       = return $ \p -> mparen (appBrackets p) e
paren _   e@(WithApp _ _ _)    = return $ \p -> mparen (withAppBrackets p) e
paren _	  e@(Ident _)	       = return $ \p -> e
paren _	  e@(Lit _)	       = return $ \p -> e
paren _	  e@(QuestionMark _ _) = return $ \p -> e
paren _	  e@(Underscore _ _)   = return $ \p -> e
paren _	  e@(Set _)	       = return $ \p -> e
paren _	  e@(SetN _ _)	       = return $ \p -> e
paren _	  e@(Prop _)	       = return $ \p -> e
paren _	  e@(Paren _ _)	       = return $ \p -> e
paren _	  e@(As _ _ _)	       = return $ \p -> e
paren _	  e@(Dot _ _)	       = return $ \p -> e
paren _	  e@(Absurd _)	       = return $ \p -> e
paren _	  e@(RawApp _ _)       = __IMPOSSIBLE__
paren _	  e@(HiddenArg _ _)    = __IMPOSSIBLE__

mparen :: Bool -> Expr -> Expr
mparen True  e = Paren (getRange e) e
mparen False e = e

