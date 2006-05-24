
{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Syntax.Internal").
-}
module Syntax.Abstract
    ( module Syntax.Abstract
    , module Syntax.Abstract.Name
    ) where

import Syntax.Info
import Syntax.Common
import Syntax.Position
import Syntax.Abstract.Name
import Syntax.Literal

data Expr
        = Var  NameInfo  Name		    -- ^ Bound variables
        | Def  NameInfo QName		    -- ^ Constants (i.e. axioms, functions, and datatypes)
        | Con  NameInfo QName		    -- ^ Constructors
	| Lit Literal			    -- ^ Literals
	| QuestionMark MetaInfo		    -- ^ meta variable for interaction
        | Underscore   MetaInfo		    -- ^ meta variable for hidden argument (must be inferred locally)
        | App  ExprInfo Expr (Arg Expr)	    -- ^
        | Lam  ExprInfo LamBinding Expr	    -- ^
        | Pi   ExprInfo TypedBinding Expr   -- ^
	| Fun  ExprInfo (Arg Expr) Expr	    -- ^ independent function space
        | Set  ExprInfo Nat		    -- ^
        | Prop ExprInfo			    -- ^
        | Let  ExprInfo [Declaration] Expr  -- ^

data Declaration
	= Axiom      DefInfo Name Expr				-- ^ postulate
	| Definition DeclInfo [TypeSignature] [Definition]	-- ^ a bunch of mutually recursive definitions
	| Module     ModuleInfo ModuleName Telescope [Declaration]
	| ModuleDef  ModuleInfo ModuleName Telescope ModuleName [Arg Expr]
	| Import     ModuleInfo ModuleName
	| Open	     DeclSource	    -- ^ this one is here only to enable translation
				    --   back to concrete syntax

-- | A definition without its type signature.
data Definition
	= FunDef     DefInfo Name [Clause]
	| DataDef    DefInfo Name [LamBinding] [Constructor]
	    -- ^ the 'LamBinding's are 'DomainFree' and binds the parameters of the datatype.

-- | Only 'Axiom's.
type TypeSignature  = Declaration
type Constructor    = TypeSignature

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
data TypedBinding = TypedBinding Range Hiding [Name] Expr
	    -- ^ . @(xs:e)@ or @{xs:e}@

type Telescope	= [TypedBinding]

-- | We could throw away @where@ clauses at this point and translate them to
--   @let@. It's not obvious how to remember that the @let@ was really a
--   @where@ clause though, so for the time being we keep it here.
data Clause	= Clause LHS RHS [Declaration]
type RHS	= Expr

data LHS	= LHS LHSInfo Name [Arg Pattern]
data Pattern	= VarP Name	-- ^ the only thing we need to know about a
				-- pattern variable is its 'Range'. This is
				-- stored in the 'Name', so we don't need a
				-- 'NameInfo' here.
		| ConP PatInfo QName [Arg Pattern]
		| WildP PatInfo

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
    getRange (Lit l)		= getRange l
    getRange (QuestionMark i)	= getRange i
    getRange (Underscore  i)	= getRange i
    getRange (App i _ _)	= getRange i
    getRange (Lam i _ _)	= getRange i
    getRange (Pi i _ _)		= getRange i
    getRange (Fun i _ _)	= getRange i
    getRange (Set i _)		= getRange i
    getRange (Prop i)		= getRange i
    getRange (Let i _ _)	= getRange i

instance HasRange Declaration where
    getRange (Axiom      i _ _	  ) = getRange i
    getRange (Definition i _ _	  ) = getRange i
    getRange (Module     i _ _ _  ) = getRange i
    getRange (ModuleDef  i _ _ _ _) = getRange i
    getRange (Import     i _	  ) = getRange i
    getRange (Open	 i	  ) = getRange i

instance HasRange Definition where
    getRange (FunDef  i _ _   ) = getRange i
    getRange (DataDef i _ _ _ ) = getRange i

instance HasRange Pattern where
    getRange (VarP x)	    = getRange x
    getRange (ConP i _ _)   = getRange i
    getRange (WildP i)	    = getRange i

instance HasRange LHS where
    getRange (LHS i _ _)    = getRange i

