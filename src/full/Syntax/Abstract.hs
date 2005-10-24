
{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Syntax.Internal").
-}
module Syntax.Abstract
    where

import Syntax.Explanation
import Syntax.Common

data Expr
	= Var Expl Name
	| Def Expl QName
	| Con Expl QName
	| Data Expl QName
	| QuestionMark Expl
	| Underscore Expl
	| App Expl Hiding Expr Expr
	| Lam Expl LamBinding Expr
	| Pi Expl TypedBinding Expr
	| Set Expl Nat
	| Prop Expl
	| Let Expl [Declaration] Expr

data Declaration
	= Axiom Expl Fixity Access Name Expr
	| FunDef Expl Fixity Access Name (Maybe Expr) [Clause]
	| DataDecl Expl Fixity Access Name Telescope Expr [Declaration]
	    -- ^ only axioms
	| Abstract Expl [Declaration]
	| Mutual Expl [Declaration]
	| Module Expl Access QName Telescope [Declaration]
	| NameSpace Expl Name Expr
	| Import Expl QName

-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Name    -- ^ . @x@ or @{x}@
	| DomainFull TypedBinding   -- ^ . @(xs:e)@ or @{xs:e}@


-- | A typed binding. Appears in dependent function spaces, typed lambdas, and
--   telescopes.
data TypedBinding = TypedBinding Expl Hiding [Name] Expr
	    -- ^ . @(xs:e)@ or @{xs:e}@

type Telescope	= [TypedBinding]

data Clause	= Clause Expl LHS RHS [Declaration]
type RHS	= Expr

data LHS	= LHS Expl Name [Argument]
data Argument	= Argument Hiding Pattern
data Pattern	= VarP Name
		| ConP Expl QName [Argument]
		| WildP Expl

