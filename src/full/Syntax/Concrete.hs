{-# OPTIONS -fglasgow-exts -cpp #-}

{-| The concrete syntax is a raw representation of the program text
    without any desugaring at all.  This is what the parser produces.
    The idea is that if we figure out how to keep the concrete syntax
    around, it can be printed exactly as the user wrote it.
-}
module Syntax.Concrete
    ( -- * Expressions
      Expr(..)
    , module Syntax.Concrete.Name
    , appView, AppView(..)
      -- * Bindings
    , LamBinding(..)
    , TypedBindings(..)
    , TypedBinding(..)
    , Telescope
      -- * Declarations
    , Declaration(..)
    , TypeSignature
    , Constructor
    , ImportDirective(..), UsingOrHiding(..), ImportedName(..)
    , LHS(..), Pattern(..)
    , RHS, WhereClause
    )
    where

import Data.Generics hiding (Fixity, Infix)

import Syntax.Position
import Syntax.Common
import Syntax.Fixity
import Syntax.Literal

import Syntax.Concrete.Name

-- | A constructor declaration is just a type signature.
type Constructor = TypeSignature


-- | Concrete expressions. Should represent exactly what the user wrote.
data Expr
	= Ident QName			    -- ^ ex: @x@
	| Lit Literal			    -- ^ ex: @1@ or @\"foo\"@
	| QuestionMark Range (Maybe Nat)    -- ^ ex: @?@ or @{! ... !}@
	| Underscore Range (Maybe Nat)	    -- ^ ex: @_@
	| App Range Expr (Arg Expr)	    -- ^ ex: @e e@ or @e {e}@
	| InfixApp Expr QName Expr	    -- ^ ex: @e + e@ (no hiding)
	| Lam Range [LamBinding] Expr	    -- ^ ex: @\\x {y} -> e@ or @\\(x:A){y:B} -> e@
	| Fun Range (Arg Expr) Expr	    -- ^ ex: @e -> e@ or @{e} -> e@
	| Pi TypedBindings Expr		    -- ^ ex: @(xs:e) -> e@ or @{xs:e} -> e@
	| Set Range			    -- ^ ex: @Set@
	| Prop Range			    -- ^ ex: @Prop@
	| SetN Range Nat		    -- ^ ex: @Set0, Set1, ..@
	| Let Range [Declaration] Expr	    -- ^ ex: @let Ds in e@
	| Paren Range Expr		    -- ^ ex: @(e)@
	| Absurd Range			    -- ^ ex: @()@ or @{}@, only in patterns
	| As Range Name Expr		    -- ^ ex: @x\@p@, only in patterns
    deriving (Typeable, Data, Eq)


-- | Concrete patterns. No literals in patterns at the moment.
data Pattern
	= IdentP QName
	| AppP Pattern (Arg Pattern)
	| InfixAppP Pattern QName Pattern
	| ParenP Range Pattern
	| WildP Range
	| AbsurdP Range
	| AsP Range Name Pattern
    deriving (Typeable, Data, Eq)


-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Name     -- ^ . @x@ or @{x}@
	| DomainFull TypedBindings   -- ^ . @(xs:e,..,ys:e')@ or @{xs:e,..,ys:e'}@
    deriving (Typeable, Data, Eq)


-- | A sequence of typed bindings with hiding information. Appears in dependent
--   function spaces, typed lambdas, and telescopes.
data TypedBindings = TypedBindings Range Hiding [TypedBinding]
	-- ^ . @(xs:e;..;ys:e')@ or @{xs:e;..;ys:e'}@
    deriving (Typeable, Data, Eq)


-- | A typed binding.
data TypedBinding
	= TBind Range [Name] Expr   -- Binding @x1,..,xn:A@
	| TNoBind Expr		    -- No binding @A@, equivalent to @_ : A@.
    deriving (Typeable, Data, Eq)


-- | A telescope is a sequence of typed bindings. Bound variables are in scope
--   in later types.
type Telescope = [TypedBindings]


{-| Left hand sides can be written in infix style. For example:

    > n + suc m = suc (n + m)
    > (f . g) x = f (g x)

    It must always be clear which name is defined, independently of fixities.
    Hence the following definition is never ok:

    > x::xs ++ ys = x :: (xs ++ ys)

-}
data LHS = LHS Range IsInfix Name [Arg Pattern]
    deriving (Typeable, Data, Eq)

type RHS	    = Expr
type WhereClause    = [Declaration]


-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective
	= ImportDirective
	    { importDirRange	:: Range
	    , usingOrHiding	:: UsingOrHiding
	    , renaming		:: [(ImportedName, Name)]
	    }
    deriving (Typeable, Data, Eq)

data UsingOrHiding
	= Hiding [ImportedName]
	| Using  [ImportedName]
    deriving (Typeable, Data, Eq)

-- | An imported name can be a module or a defined name
data ImportedName = ImportedModule  { importedName :: Name }
		  | ImportedName    { importedName :: Name }
    deriving (Typeable, Data, Eq, Ord)

instance Show ImportedName where
    show (ImportedModule x) = "module " ++ show x
    show (ImportedName   x) = show x

{--------------------------------------------------------------------------
    Declarations
 --------------------------------------------------------------------------}

-- | Just type signatures.
type TypeSignature	 = Declaration

{-| The representation type of a declaration. The comments indicate
    which type in the intended family the constructor targets.
-}
data Declaration
	= TypeSig Name Expr
	| FunClause LHS RHS WhereClause
	| Data        Range Name Telescope Expr [Constructor]
	| Infix Fixity [Name]
	| Mutual      Range [Declaration]
	| Abstract    Range [Declaration]
	| Private     Range [Declaration]
	| Postulate   Range [TypeSignature]
	| Open        Range QName ImportDirective
	| Import      Range QName (Maybe Name) ImportDirective
	| ModuleMacro Range  Name Telescope Expr ImportDirective
	| Module      Range QName Telescope [Declaration]
    deriving (Eq, Typeable, Data)


{--------------------------------------------------------------------------
    Views
 --------------------------------------------------------------------------}

-- | The 'Expr' is not an application.
data AppView = AppView Expr [Arg Expr]

appView :: Expr -> AppView
appView (App r e1 e2) = vApp (appView e1) e2
    where
	vApp (AppView e es) arg = AppView e (es ++ [arg])
appView e = AppView e []

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance HasRange Expr where
    getRange e =
	case e of
	    Ident x		-> getRange x
	    Lit x		-> getRange x
	    QuestionMark r _	-> r
	    Underscore r _	-> r
	    App r _ _		-> r
	    InfixApp e1 _ e2	-> fuseRange e1 e2
	    Lam r _ _		-> r
	    Fun r _ _		-> r
	    Pi b e		-> fuseRange b e
	    Set r		-> r
	    Prop r		-> r
	    SetN r _		-> r
	    Let r _ _		-> r
	    Paren r _		-> r
	    As r _ _		-> r
	    Absurd r		-> r

instance HasRange TypedBindings where
    getRange (TypedBindings r _ _) = r

instance HasRange TypedBinding where
    getRange (TBind r _ _) = r
    getRange (TNoBind e)   = getRange e

instance HasRange LamBinding where
    getRange (DomainFree _ x)	= getRange x
    getRange (DomainFull b)	= getRange b

instance HasRange Declaration where
    getRange (TypeSig x t)		= fuseRange x t
    getRange (FunClause lhs rhs [])	= fuseRange lhs rhs
    getRange (FunClause lhs rhs wh)	= fuseRange lhs (last wh)
    getRange (Data r _ _ _ _)		= r
    getRange (Mutual r _)		= r
    getRange (Abstract r _)		= r
    getRange (Open r _ _)		= r
    getRange (ModuleMacro r _ _ _ _)	= r
    getRange (Import r _ _ _)		= r
    getRange (Private r _)		= r
    getRange (Postulate r _)		= r
    getRange (Module r _ _ _)		= r
    getRange (Infix f _)		= getRange f

instance HasRange LHS where
    getRange (LHS r _ _ _)  = r

instance HasRange UsingOrHiding where
    getRange (Using xs)	    = getRange xs
    getRange (Hiding xs)    = getRange xs

instance HasRange ImportDirective where
    getRange = importDirRange

instance HasRange ImportedName where
    getRange (ImportedName x)	= getRange x
    getRange (ImportedModule x)	= getRange x

instance HasRange Pattern where
    getRange (IdentP x)		= getRange x
    getRange (AppP p q)		= fuseRange p q
    getRange (InfixAppP p _ q)	= fuseRange p q
    getRange (ParenP r _)	= r
    getRange (WildP r)		= r
    getRange (AsP r _ _)	= r
    getRange (AbsurdP r)	= r

