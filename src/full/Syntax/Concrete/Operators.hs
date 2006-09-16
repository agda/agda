{-# OPTIONS -fglasgow-exts -cpp #-}

{-| The parser doesn't know about operators and parses everything as normal
    function application. This module contains the functions that parses the
    operators properly. For a stand-alone implementation of this see
    @src/prototyping/mixfix@.

    It also contains the function that puts parenthesis back given the
    precedence of the context.
-}
module Syntax.Concrete.Operators
    ( OperatorException(..)
    , parseApplication
    , parsePattern
    , paren
    , mparen
    ) where

import Prelude hiding (putStrLn)
import Utils.IO

import Control.Monad.Trans
import Control.Exception
import Data.Typeable
import qualified Data.Map as Map
import Data.List

import Syntax.Concrete.Pretty ()
import Syntax.Common
import Syntax.Concrete
import Syntax.Concrete.Operators.Parser
import Syntax.Position
import Syntax.Fixity
import Syntax.Scope

import Utils.ReadP
import Utils.Monad

#include "../../undefined.h"

---------------------------------------------------------------------------
-- * Exceptions
---------------------------------------------------------------------------

-- | Thrown by 'parseApplication' if the correct bracketing cannot be deduced.
data OperatorException
	= NoParseForApplication [Expr]
	| AmbiguousParseForApplication [Expr] [Expr]
    deriving (Typeable, Show)

instance HasRange OperatorException where
    getRange (NoParseForApplication es)		 = getRange es
    getRange (AmbiguousParseForApplication es _) = getRange es

---------------------------------------------------------------------------
-- * Building the parser
---------------------------------------------------------------------------

localNames :: ScopeM ([Name], [Operator])
localNames = do
    scope <- getScopeInfo
    let public  = publicNameSpace scope
	private = privateNameSpace scope
	local	= localVariables scope
	(names, ops) = split $ concatMap namespaceOps [public, private]
    return (Map.keys local ++ names, ops)
    where
	namespaceOps = map operator . Map.elems . definedNames

	split ops = ([ x | Left x <- zs], [ y | Right y <- zs ])
	    where
		zs = concatMap opOrNot ops

	opOrNot (Operator (NameDecl [x]) _) = [Left x]
	opOrNot op@(Operator d _)	    = [Left (nameDeclName d), Right op]

buildParser :: ScopeM (OpP Expr)
buildParser = do
    (names, ops) <- localNames
    let (non, fix) = partition nonfix ops
    return $ recursive $ \p ->
	map (mkP p) (order fix)
	++ [ appP p ]
	++ map (nonfixP . opP p) non
	++ [ const $ choice $ otherP : map identP names ]
    where
	operator (Operator op _) = op
	fixity   (Operator _  f) = f
	level = fixityLevel . fixity

	isinfixl (Operator op (LeftAssoc _ _))	= isInfix op
	isinfixl _				= False

	isinfixr (Operator op (RightAssoc _ _)) = isInfix op
	isinfixr _				= False

	isinfix (Operator op (NonAssoc _ _))	= isInfix op
	isinfix _				= False

	on f g x y = f (g x) (g y)

	nonfix = isNonfix . operator
	order = groupBy ((==) `on` level) . sortBy (flip compare `on` level)

	mkP p0 ops = choice' [infx, inlfx, inrfx, prefx, postfx, id]
	    where
		choice' = foldr1 (++++)
		f ++++ g = \p -> f p +++ g p
		inlfx	= fixP infixP   isinfixl
		inrfx	= fixP infixP   isinfixr
		infx	= fixP infixP   isinfix
		prefx	= fixP prefixP  (isPrefix . operator)
		postfx	= fixP postfixP (isPostfix . operator)

		fixP :: (OpP Expr -> OpP Expr -> OpP Expr) -> (Operator -> Bool) -> OpP Expr -> OpP Expr
		fixP f g = f $ choice $ map (opP p0) $ filter g ops

---------------------------------------------------------------------------
-- * Parse functions
---------------------------------------------------------------------------

parsePattern :: [Pattern] -> ScopeM Pattern
parsePattern es = return $ foldl1 app es
    where
	app e1 (HiddenP r e2) = AppP e1 (Arg Hidden e2)
	app e1 e2	      = AppP e1 (Arg NotHidden e2)

parseApplication :: [Expr] -> ScopeM Expr
parseApplication es = do
    p <- buildParser
    case parse p es of
	[e] -> return e
	[]  -> throwDyn $ NoParseForApplication es
	es' -> throwDyn $ AmbiguousParseForApplication es es'

-- Inserting parenthesis --------------------------------------------------

paren :: (Name -> Operator) -> Expr -> Precedence -> Expr
paren _   e@(App _ _ _)	       p = mparen (appBrackets p) e
paren f	  e@(OpApp _ op _)     p = mparen (opBrackets (f $ nameDeclName op) p) e
paren _   e@(Lam _ _ _)	       p = mparen (lamBrackets p) e
paren _   e@(Fun _ _ _)	       p = mparen (lamBrackets p) e
paren _   e@(Pi _ _)	       p = mparen (lamBrackets p) e
paren _   e@(Let _ _ _)	       p = mparen (lamBrackets p) e
paren _	  e@(Ident _)	       p = e
paren _	  e@(Lit _)	       p = e
paren _	  e@(QuestionMark _ _) p = e
paren _	  e@(Underscore _ _)   p = e
paren _	  e@(Set _)	       p = e
paren _	  e@(SetN _ _)	       p = e
paren _	  e@(Prop _)	       p = e
paren _	  e@(Paren _ _)	       p = e
paren _	  e@(List _ _)	       p = e
paren _	  e@(As _ _ _)	       p = e
paren _	  e@(Absurd _)	       p = e
paren _	  e@(RawApp _ _)       p = __IMPOSSIBLE__
paren _	  e@(HiddenArg _ _)    p = __IMPOSSIBLE__

mparen True  e = Paren (getRange e) e
mparen False e = e

