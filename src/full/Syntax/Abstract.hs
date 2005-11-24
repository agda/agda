
{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Syntax.Internal").
-}
module Syntax.Abstract
    where

import Syntax.Info
import Syntax.Common

data Expr
        = Var  NameInfo  Name         -- ^ Bound variables
        | Def  NameInfo QName         -- ^ Defined constants
        | Con  NameInfo QName         -- ^ Constructors
        | Data NameInfo QName         -- ^ Names of datatypes
	| Lit Literal		      -- ^ Literals
        | QuestionMark Info           -- ^ meta variable for interaction
        | Underscore   Info           -- ^ meta variable for hidden argument (must be inferred locally)
        | App  Info Hiding Expr Expr  -- ^ Hiding says if this is an hidden application (@s {t}@) or a normal application (@s t@).
        | Lam  Info LamBinding Expr   -- ^ 
        | Pi   Info TypedBinding Expr -- ^ 
        | Set  Info Nat               -- ^ 
        | Prop Info                   -- ^ 
        | Let  Info [Declaration] Expr-- ^ 

-- | what is Info used for (above and below)? which invariants apply?

data Declaration
	= Axiom     Info Fixity Access Name Expr
	| FunDef    Info Fixity Access Name (Maybe Expr) [Clause]
	| DataDecl  Info Fixity Access Name Telescope Expr [Declaration]
	    -- ^ only axioms
	| Abstract  Info [Declaration]
	| Mutual    Info [Declaration]
	| Module    Info Access QName Telescope [Declaration]
	| NameSpace Info Name Expr
	| Import    Info QName

-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Name    -- ^ . @x@ or @{x}@
	| DomainFull TypedBinding   -- ^ . @(xs:e)@ or @{xs:e}@


-- | A typed binding. Appears in dependent function spaces, typed lambdas, and
--   telescopes. I might be tempting to simplify this to only bind a single
--   name at a time. This would mean that we would have to typecheck the type
--   several times (@(x,y:A)@ vs. @(x:A)(y:A)@). In most cases this wouldn't
--   really be a problem, but it's good principle to not do extra work unless
--   you have to.
data TypedBinding = TypedBinding Info Hiding [Name] Expr
	    -- ^ . @(xs:e)@ or @{xs:e}@

type Telescope	= [TypedBinding]

data Clause	= Clause Info LHS RHS [Declaration]
type RHS	= Expr

data LHS	= LHS Info Name [Argument]
data Argument	= Argument Hiding Pattern
data Pattern	= VarP Name
		| ConP Info QName [Argument]
		| WildP Info

-- | why has Var in Expr above a NameInfo but VarP no Info?
-- | why has Con in Expr above a NameInfo but ConP an Info?
-- | why Underscore above and WildP here? (UnderscoreP better?)
