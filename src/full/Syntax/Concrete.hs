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
    , TypedBinding(..)
    , Telescope
      -- * Declarations
    , Declaration(..)
    , TopLevelDeclaration
    , TypeSignature
    , LocalDeclaration, PrivateDeclaration
    , MutualDeclaration, AbstractDeclaration
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
	| App Range Hiding Expr Expr	    -- ^ ex: @e e@ or @e {e}@
	| InfixApp Expr QName Expr	    -- ^ ex: @e + e@ (no hiding)
	| Lam Range [LamBinding] Expr	    -- ^ ex: @\\x {y} -> e@ or @\\(x:A){y:B} -> e@
	| Fun Range Hiding Expr Expr	    -- ^ ex: @e -> e@ or @{e} -> e@
	| Pi TypedBinding Expr		    -- ^ ex: @(xs:e) -> e@ or @{xs:e} -> e@
	| Set Range			    -- ^ ex: @Set@
	| Prop Range			    -- ^ ex: @Prop@
	| SetN Range Nat		    -- ^ ex: @Set0, Set1, ..@
	| Let Range [LocalDeclaration] Expr -- ^ ex: @let Ds in e@
	| Paren Range Expr		    -- ^ ex: @(e)@
    deriving (Typeable, Data, Eq)


-- | Concrete patterns. No literals in patterns at the moment.
data Pattern
	= IdentP QName
	| AppP Hiding Pattern Pattern
	| InfixAppP Pattern QName Pattern
	| ParenP Range Pattern
	| WildP Range
    deriving (Typeable, Data, Eq)


-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Name    -- ^ . @x@ or @{x}@
	| DomainFull TypedBinding   -- ^ . @(xs:e)@ or @{xs:e}@
    deriving (Typeable, Data, Eq)


-- | A typed binding. Appears in dependent function spaces, typed lambdas, and
--   telescopes.
data TypedBinding
	= TypedBinding Range Hiding [Name] Expr
	    -- ^ . @(xs:e)@ or @{xs:e}@
    deriving (Typeable, Data, Eq)


-- | A telescope is a sequence of typed bindings. Bound variables are in scope
--   in later types.
type Telescope = [TypedBinding]


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
type WhereClause    = [LocalDeclaration]


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

-- | Declarations that can appear in a 'Let' or a 'WhereClause'.
type LocalDeclaration	 = Declaration

-- | Declarations that can appear in a 'Private' block.
type PrivateDeclaration	 = Declaration

-- | Declarations that can appear in a 'Mutual' block.
type MutualDeclaration	 = Declaration

-- | Declarations that can appear in a 'Abstract' block.
type AbstractDeclaration = Declaration

-- | Everything can appear at top-level.
type TopLevelDeclaration = Declaration

{-| The representation type of a declaration. The comments indicate
    which type in the intended family the constructor targets.
-}
data Declaration
	= TypeSig Name Expr
	| FunClause LHS RHS WhereClause
	| Data        Range Name Telescope Expr [Constructor]
	| Infix Fixity [Name]
	| Mutual      Range [MutualDeclaration]
	| Abstract    Range [AbstractDeclaration]
	| Private     Range [PrivateDeclaration]
	| Postulate   Range [TypeSignature]
	| Open        Range QName ImportDirective
	| Import      Range QName (Maybe Name) ImportDirective
	| ModuleMacro Range  Name Telescope Expr ImportDirective
	| Module      Range QName Telescope [TopLevelDeclaration]
    deriving (Eq, Typeable, Data)


{--------------------------------------------------------------------------
    Views
 --------------------------------------------------------------------------}

-- | The 'Expr' is not an application.
data AppView = AppView Expr [Arg Expr]

appView :: Expr -> AppView
appView (App r h e1 e2) = vApp (appView e1) (Arg h e2)
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
	    App r _ _ _		-> r
	    InfixApp e1 _ e2	-> fuseRange e1 e2
	    Lam r _ _		-> r
	    Fun r _ _ _		-> r
	    Pi b e		-> fuseRange b e
	    Set r		-> r
	    Prop r		-> r
	    SetN r _		-> r
	    Let r _ _		-> r
	    Paren r _		-> r

instance HasRange TypedBinding where
    getRange (TypedBinding r _ _ _) = r

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
    getRange (AppP _ p q)	= fuseRange p q
    getRange (InfixAppP p _ q)	= fuseRange p q
    getRange (ParenP r _)	= r
    getRange (WildP r)		= r

