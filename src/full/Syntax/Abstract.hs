
{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Syntax.Internal").
-}
module Syntax.Abstract
    where

import Syntax.Info
import Syntax.Common
import Syntax.Position

data Expr
        = Var  NameInfo  Name		    -- ^ Bound variables
        | Def  NameInfo QName		    -- ^ Defined constants
        | Con  NameInfo QName		    -- ^ Constructors
        | Data NameInfo QName		    -- ^ Names of datatypes
	| Lit Literal			    -- ^ Literals
	| QuestionMark MetaInfo		    -- ^ meta variable for interaction
        | Underscore   MetaInfo		    -- ^ meta variable for hidden argument (must be inferred locally)
        | App  ExprInfo Hiding Expr Expr    -- ^ Hiding says if this is an hidden application (@s {t}@) or a normal application (@s t@).
        | Lam  ExprInfo LamBinding Expr	    -- ^ 
        | Pi   ExprInfo TypedBinding Expr   -- ^ 
        | Set  ExprInfo Nat		    -- ^ 
        | Prop ExprInfo			    -- ^ 
        | Let  ExprInfo [Declaration] Expr  -- ^ 
    deriving (Show)

-- | what is Info used for (above and below)? which invariants apply?

data Declaration
	= Axiom     DefInfo Name Expr
	| FunDef    DefInfo Name (Maybe Expr) [Clause]
	| DataDecl  DefInfo Name Telescope Expr [Declaration]
	    -- ^ only axioms
	| Abstract  DeclInfo [Declaration]
	| Mutual    DeclInfo [Declaration]
	| Module    DefInfo QName Telescope [Declaration]
	| ModuleDef DefInfo Name  Telescope QName [Arg Expr]
	| Import    DeclInfo QName
    deriving (Show)

-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Name    -- ^ . @x@ or @{x}@
	| DomainFull TypedBinding   -- ^ . @(xs:e)@ or @{xs:e}@
    deriving (Show)


-- | A typed binding. Appears in dependent function spaces, typed lambdas, and
--   telescopes. I might be tempting to simplify this to only bind a single
--   name at a time. This would mean that we would have to typecheck the type
--   several times (@(x,y:A)@ vs. @(x:A)(y:A)@). In most cases this wouldn't
--   really be a problem, but it's good principle to not do extra work unless
--   you have to.
data TypedBinding = TypedBinding Range Hiding [Name] Expr
	    -- ^ . @(xs:e)@ or @{xs:e}@
    deriving (Show)

type Telescope	= [TypedBinding]

-- | We could throw away @where@ clauses at this point and translate them to
--   @let@. It's not obvious how to remember that the @let@ was really a
--   @where@ clause though, so for the time being we keep it here.
data Clause	= Clause LHS RHS [Declaration]
    deriving (Show)
type RHS	= Expr

data LHS	= LHS LHSInfo Name [Arg Pattern]
    deriving (Show)
data Pattern	= VarP Name	-- ^ the only thing we need to know about a
				-- pattern variable is its 'Range'. This is
				-- stored in the 'Name', so we don't need a
				-- 'NameInfo' here.
		| ConP PatInfo QName [Arg Pattern]
		| WildP PatInfo
    deriving Show

-- | why has Var in Expr above a NameInfo but VarP no Info?
-- | why has Con in Expr above a NameInfo but ConP an Info?
-- | why Underscore above and WildP here? (UnderscoreP better?)


{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance HasRange LamBinding where
    getRange (DomainFree _ x) = getRange x
    getRange (DomainFull b)   = getRange b

instance HasRange TypedBinding where
    getRange (TypedBinding r _ _ _) = r

instance HasRange Expr where
    getRange (Var i _)		= getRange i
    getRange (Def i _)		= getRange i
    getRange (Con i _)		= getRange i
    getRange (Data i _)		= getRange i
    getRange (Lit l)		= getRange l
    getRange (QuestionMark i)	= getRange i
    getRange (Underscore  i)	= getRange i
    getRange (App i _ _ _)	= getRange i
    getRange (Lam i _ _)	= getRange i
    getRange (Pi i _ _)		= getRange i
    getRange (Set i _)		= getRange i
    getRange (Prop i)		= getRange i
    getRange (Let i _ _)	= getRange i

instance HasRange Declaration where
    getRange (Axiom     i _ _	  ) = getRange i
    getRange (FunDef    i _ _ _	  ) = getRange i
    getRange (DataDecl  i _ _ _ _ ) = getRange i
    getRange (Abstract  i _	  ) = getRange i
    getRange (Mutual    i _	  ) = getRange i
    getRange (Module    i _ _ _	  ) = getRange i
    getRange (ModuleDef i _ _ _ _ ) = getRange i
    getRange (Import    i _	  ) = getRange i

instance HasRange Pattern where
    getRange (VarP x)	    = getRange x
    getRange (ConP i _ _)   = getRange i
    getRange (WildP i)	    = getRange i

instance HasRange LHS where
    getRange (LHS i _ _)    = getRange i

