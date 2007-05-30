{-# OPTIONS -fglasgow-exts #-}

{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Syntax.Internal").
-}
module Syntax.Abstract
    ( module Syntax.Abstract
    , module Syntax.Abstract.Name
    ) where

import Prelude hiding (foldr)
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.Map (Map)
import Data.Generics (Typeable, Data)

import qualified Syntax.Concrete as C
import Syntax.Info
import Syntax.Common
import Syntax.Position
import Syntax.Abstract.Name
import Syntax.Literal
import Syntax.Scope.Base

data Expr
        = Var  Name			     -- ^ Bound variables
        | Def  QName			     -- ^ Constants (i.e. axioms, functions, and datatypes)
        | Con  QName			     -- ^ Constructors
	| Lit Literal			     -- ^ Literals
	| QuestionMark MetaInfo		     -- ^ meta variable for interaction
        | Underscore   MetaInfo		     -- ^ meta variable for hidden argument (must be inferred locally)
        | App  ExprInfo Expr (NamedArg Expr) -- ^
	| WithApp ExprInfo Expr [Expr]	     -- ^ with application
        | Lam  ExprInfo LamBinding Expr	     -- ^
        | Pi   ExprInfo Telescope Expr	     -- ^
	| Fun  ExprInfo (Arg Expr) Expr	     -- ^ independent function space
        | Set  ExprInfo Nat		     -- ^
        | Prop ExprInfo			     -- ^
        | Let  ExprInfo [LetBinding] Expr    -- ^
	| Rec  ExprInfo [(C.Name, Expr)]     -- ^ record construction
	| ScopedExpr ScopeInfo Expr	     -- ^ scope annotation
  deriving (Typeable, Data)

data Declaration
	= Axiom      DefInfo QName Expr				-- ^ postulate
	| Primitive  DefInfo QName Expr				-- ^ primitive function
	| Definition DeclInfo [TypeSignature] [Definition]	-- ^ a bunch of mutually recursive definitions
	| Section    ModuleInfo ModuleName [TypedBindings] [Declaration]
	| Apply	     ModuleInfo ModuleName [TypedBindings] ModuleName [NamedArg Expr] (Map QName QName) (Map ModuleName ModuleName)
	| Import     ModuleInfo ModuleName
	| Pragma     Range	Pragma
	| ScopedDecl ScopeInfo [Declaration]  -- ^ scope annotation
  deriving (Typeable, Data)

data Pragma = OptionsPragma [String]
	    | BuiltinPragma String Expr
  deriving (Typeable, Data)

data LetBinding = LetBind LetInfo Name Expr Expr    -- ^ LetBind info name type defn
  deriving (Typeable, Data)

-- | A definition without its type signature.
data Definition
	= FunDef     DefInfo QName [Clause]
	| DataDef    DefInfo QName [LamBinding] [Constructor]
	    -- ^ the 'LamBinding's are 'DomainFree' and binds the parameters of the datatype.
	| RecDef     DefInfo QName [LamBinding] [Field]
  deriving (Typeable, Data)

-- | Only 'Axiom's.
type TypeSignature  = Declaration
type Constructor    = TypeSignature
type Field	    = TypeSignature

-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Name    -- ^ . @x@ or @{x}@
	| DomainFull TypedBindings  -- ^ . @(xs:e)@ or @{xs:e}@
  deriving (Typeable, Data)

-- | Typed bindings with hiding information.
data TypedBindings = TypedBindings Range Hiding [TypedBinding]
	    -- ^ . @(xs:e;..;ys:e')@ or @{xs:e;..;ys:e'}@
  deriving (Typeable, Data)

-- | A typed binding. Appears in dependent function spaces, typed lambdas, and
--   telescopes. I might be tempting to simplify this to only bind a single
--   name at a time. This would mean that we would have to typecheck the type
--   several times (@x,y:A@ vs. @x:A; y:A@). In most cases this wouldn't
--   really be a problem, but it's good principle to not do extra work unless
--   you have to.
data TypedBinding = TBind Range [Name] Expr
		  | TNoBind Expr
  deriving (Typeable, Data)

type Telescope	= [TypedBindings]

-- | We could throw away @where@ clauses at this point and translate them to
--   @let@. It's not obvious how to remember that the @let@ was really a
--   @where@ clause though, so for the time being we keep it here.
data Clause	= Clause LHS RHS [Declaration]
  deriving (Typeable, Data)
data RHS	= RHS Expr
		| AbsurdRHS
		| WithRHS [Expr] [Clause]
  deriving (Typeable, Data)

data LHS	= LHS LHSInfo QName [NamedArg Pattern] [Pattern]
  deriving (Typeable, Data)

-- | Parameterised over the type of dot patterns.
data Pattern' e	= VarP Name
		| ConP PatInfo QName [NamedArg (Pattern' e)]
		| DefP PatInfo QName [NamedArg (Pattern' e)]  -- ^ defined pattern
		| WildP PatInfo
		| AsP PatInfo Name (Pattern' e)
		| DotP PatInfo e
		| AbsurdP PatInfo
		| LitP Literal
		| ImplicitP PatInfo	-- ^ generated at type checking for implicit arguments
  deriving (Typeable, Data)

type Pattern = Pattern' Expr

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance Functor Pattern' where
    fmap f p = case p of
	VarP x	    -> VarP x
	ConP i c ps -> ConP i c $ (fmap . fmap . fmap . fmap) f ps
	DefP i c ps -> DefP i c $ (fmap . fmap . fmap . fmap) f ps
	LitP l	    -> LitP l
	AsP i x p   -> AsP i x $ fmap f p
	DotP i e    -> DotP i (f e)
	AbsurdP i   -> AbsurdP i
	WildP i	    -> WildP i
	ImplicitP i -> ImplicitP i

-- foldr should really take its arguments in a different order!
instance Foldable Pattern' where
    foldr f z p = case p of
	VarP _	    -> z
	ConP _ _ ps -> (foldrF . foldrF . foldrF . foldrF) f ps z
	DefP _ _ ps -> (foldrF . foldrF . foldrF . foldrF) f ps z
	LitP _	    -> z
	AsP _ _ p   -> foldr f z p
	DotP _ e    -> f e z
	AbsurdP _   -> z
	WildP _	    -> z
	ImplicitP _ -> z
	where
	    foldrF f = flip (foldr f)

instance Traversable Pattern' where
    traverse f p = case p of
	VarP x	    -> pure $ VarP x
	ConP i c ps -> ConP i c <$> (traverse . traverse . traverse . traverse) f ps
	DefP i c ps -> DefP i c <$> (traverse . traverse . traverse . traverse) f ps
	LitP l	    -> pure $ LitP l
	AsP i x p   -> AsP i x <$> traverse f p
	DotP i e    -> DotP i <$> f e
	AbsurdP i   -> pure $ AbsurdP i
	WildP i	    -> pure $ WildP i
	ImplicitP i -> pure $ ImplicitP i

instance HasRange LamBinding where
    getRange (DomainFree _ x) = getRange x
    getRange (DomainFull b)   = getRange b

instance HasRange TypedBindings where
    getRange (TypedBindings r _ _) = r

instance HasRange TypedBinding where
    getRange (TBind r _ _) = r
    getRange (TNoBind e)   = getRange e

instance HasRange Expr where
    getRange (Var x)		= getRange x
    getRange (Def x)		= getRange x
    getRange (Con x)		= getRange x
    getRange (Lit l)		= getRange l
    getRange (QuestionMark i)	= getRange i
    getRange (Underscore  i)	= getRange i
    getRange (App i _ _)	= getRange i
    getRange (WithApp i _ _)	= getRange i
    getRange (Lam i _ _)	= getRange i
    getRange (Pi i _ _)		= getRange i
    getRange (Fun i _ _)	= getRange i
    getRange (Set i _)		= getRange i
    getRange (Prop i)		= getRange i
    getRange (Let i _ _)	= getRange i
    getRange (Rec i _)		= getRange i
    getRange (ScopedExpr _ e)	= getRange e

instance HasRange Declaration where
    getRange (Axiom      i _ _	       ) = getRange i
    getRange (Definition i _ _	       ) = getRange i
    getRange (Section    i _ _ _       ) = getRange i
    getRange (Apply	 i _ _ _ _ _ _ ) = getRange i
    getRange (Import     i _	       ) = getRange i
    getRange (Primitive  i _ _	       ) = getRange i
    getRange (Pragma	 i _	       ) = getRange i
    getRange (ScopedDecl _ d	       ) = getRange d

instance HasRange Definition where
    getRange (FunDef  i _ _   ) = getRange i
    getRange (DataDef i _ _ _ ) = getRange i
    getRange (RecDef  i _ _ _ ) = getRange i

instance HasRange (Pattern' e) where
    getRange (VarP x)	   = getRange x
    getRange (ConP i _ _)  = getRange i
    getRange (DefP i _ _)  = getRange i
    getRange (WildP i)	   = getRange i
    getRange (ImplicitP i) = getRange i
    getRange (AsP i _ _)   = getRange i
    getRange (DotP i _)    = getRange i
    getRange (AbsurdP i)   = getRange i
    getRange (LitP l)	   = getRange l

instance HasRange LHS where
    getRange (LHS i _ _ _) = getRange i

instance HasRange Clause where
    getRange (Clause lhs rhs ds) = getRange (lhs,rhs,ds)

instance HasRange RHS where
    getRange AbsurdRHS	    = noRange
    getRange (RHS e)	    = getRange e
    getRange (WithRHS e cs) = fuseRange e cs

instance HasRange LetBinding where
    getRange (LetBind i _ _ _) = getRange i

