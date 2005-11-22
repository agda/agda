
{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Syntax.Internal").
-}
module Syntax.Abstract
    where

import Syntax.Explanation
import Syntax.Common

data Expr
        = Var  NameExpl  Name         -- ^ Variables
        | Def  NameExpl QName         -- ^ Defined name (~=bound variable)
        | Con  NameExpl QName         -- ^ Constructors
        | Data NameExpl QName         -- ^ Defined name repr. a datatype(?)
        | QuestionMark Expl           -- ^ meta variable for interaction
        | Underscore   Expl           -- ^ meta variable for hidden argument (must be inferred locally)
        | App  Expl Hiding Expr Expr  -- ^ Hiding tells if the argument (second Expr) should be hidden
        | Lam  Expl LamBinding Expr   -- ^ 
        | Pi   Expl TypedBinding Expr -- ^ 
        | Set  Expl Nat               -- ^ 
        | Prop Expl                   -- ^ 
        | Let  Expl [Declaration] Expr-- ^ 

-- | what is Expl used for (above and below)? which invariants apply?

data Declaration
	= Axiom     Expl Fixity Access Name Expr
	| FunDef    Expl Fixity Access Name (Maybe Expr) [Clause]
	| DataDecl  Expl Fixity Access Name Telescope Expr [Declaration]
	    -- ^ only axioms
	| Abstract  Expl [Declaration]
	| Mutual    Expl [Declaration]
	| Module    Expl Access QName Telescope [Declaration]
	| NameSpace Expl Name Expr
	| Import    Expl QName

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

-- | why has Var in Expr above a NameExpl but VarP no Expl?
-- | why has Con in Expr above a NameExpl but ConP an Expl?
-- | why Underscore above and WildP here? (UnderscoreP better?)
