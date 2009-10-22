{-# LANGUAGE CPP, DeriveDataTypeable #-}

{-| The concrete syntax is a raw representation of the program text
    without any desugaring at all.  This is what the parser produces.
    The idea is that if we figure out how to keep the concrete syntax
    around, it can be printed exactly as the user wrote it.
-}
module Agda.Syntax.Concrete
    ( -- * Expressions
      Expr(..)
    , module Agda.Syntax.Concrete.Name
    , appView, AppView(..)
      -- * Bindings
    , LamBinding(..)
    , TypedBindings(..)
    , TypedBinding(..)
    , BoundName(..), mkBoundName_
    , Telescope -- (..)
      -- * Declarations
    , Declaration(..)
    , TypeSignature
    , Constructor
    , Field
    , ImportDirective(..), UsingOrHiding(..), ImportedName(..)
    , Renaming(..), AsName(..)
    , defaultImportDir
    , OpenShortHand(..)
    , LHS(..), Pattern(..)
    , RHS(..), WhereClause(..)
    , Pragma(..)
    , Module
    , topLevelModuleName
    )
    where

import Data.Generics hiding (Fixity, Infix)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Literal

import Agda.Syntax.Concrete.Name

import Agda.Utils.Impossible
#include "../undefined.h"

-- | Concrete expressions. Should represent exactly what the user wrote.
data Expr
	= Ident QName			       -- ^ ex: @x@
	| Lit Literal			       -- ^ ex: @1@ or @\"foo\"@
	| QuestionMark !Range (Maybe Nat)      -- ^ ex: @?@ or @{! ... !}@
	| Underscore !Range (Maybe Nat)	       -- ^ ex: @_@
	| RawApp !Range [Expr]		       -- ^ before parsing operators
	| App !Range Expr (NamedArg Expr)      -- ^ ex: @e e@, @e {e}@, or @e {x = e}@
	| OpApp !Range Name [Expr]	       -- ^ ex: @e + e@
        | WithApp !Range Expr [Expr]           -- ^ ex: @e | e1 | .. | en@
	| HiddenArg !Range (Named String Expr) -- ^ ex: @{e}@ or @{x=e}@
	| Lam !Range [LamBinding] Expr	       -- ^ ex: @\\x {y} -> e@ or @\\(x:A){y:B} -> e@
        | AbsurdLam !Range Hiding              -- ^ ex: @\\ ()@
	| Fun !Range Expr Expr		       -- ^ ex: @e -> e@ or @{e} -> e@
	| Pi Telescope Expr		       -- ^ ex: @(xs:e) -> e@ or @{xs:e} -> e@
	| Set !Range			       -- ^ ex: @Set@
	| Prop !Range			       -- ^ ex: @Prop@
	| SetN !Range Nat		       -- ^ ex: @Set0, Set1, ..@
	| Rec !Range [(Name, Expr)]	       -- ^ ex: @record {x = a; y = b}@
	| Let !Range [Declaration] Expr	       -- ^ ex: @let Ds in e@
	| Paren !Range Expr		       -- ^ ex: @(e)@
	| Absurd !Range			       -- ^ ex: @()@ or @{}@, only in patterns
	| As !Range Name Expr		       -- ^ ex: @x\@p@, only in patterns
	| Dot !Range Expr		       -- ^ ex: @.p@, only in patterns
        | ETel Telescope                       -- ^ only used for printing telescopes
    deriving (Typeable, Data, Eq)


-- | Concrete patterns. No literals in patterns at the moment.
data Pattern
	= IdentP QName
	| AppP Pattern (NamedArg Pattern)
	| RawAppP !Range [Pattern]
	| OpAppP !Range Name [Pattern]
	| HiddenP !Range (Named String Pattern)
	| ParenP !Range Pattern
	| WildP !Range
	| AbsurdP !Range
	| AsP !Range Name Pattern
	| DotP !Range Expr
	| LitP Literal
    deriving (Typeable, Data, Eq)


-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding BoundName -- ^ . @x@ or @{x}@
	| DomainFull TypedBindings    -- ^ . @(xs:e,..,ys:e')@ or @{xs:e,..,ys:e'}@
    deriving (Typeable, Data, Eq)


-- | A sequence of typed bindings with hiding information. Appears in dependent
--   function spaces, typed lambdas, and telescopes.
data TypedBindings = TypedBindings !Range Hiding [TypedBinding]
	-- ^ . @(xs:e;..;ys:e')@ or @{xs:e;..;ys:e'}@
    deriving (Typeable, Data, Eq)


data BoundName = BName { boundName   :: Name
                       , bnameFixity :: Fixity
                       }
    deriving (Typeable, Data, Eq)

mkBoundName_ :: Name -> BoundName
mkBoundName_ x = BName x defaultFixity

-- | A typed binding.
data TypedBinding
	= TBind !Range [BoundName] Expr   -- Binding @x1,..,xn:A@
	| TNoBind Expr		    -- No binding @A@, equivalent to @_ : A@.
    deriving (Typeable, Data, Eq)


-- | A telescope is a sequence of typed bindings. Bound variables are in scope
--   in later types. Or it's the mysterious Thierry-function-telescope. Only it's not.
type Telescope = [TypedBindings]
-- data Telescope = TeleBind [TypedBindings]
-- 	       | TeleFun Telescope Telescope
--     deriving (Typeable, Data, Eq)


{-| Left hand sides can be written in infix style. For example:

    > n + suc m = suc (n + m)
    > (f ∘ g) x = f (g x)

   We use fixity information to see which name is actually defined.
-}
data LHS = LHS Pattern [Pattern] [RewriteEqn] [WithExpr]
         -- ^ original pattern, with-patterns, rewrite equations and with-expressions
         | Ellipsis Range [Pattern] [RewriteEqn] [WithExpr]
         -- ^ new with-patterns, rewrite equations and with-expressions
  deriving (Typeable, Data, Eq)

type RewriteEqn = Expr
type WithExpr   = Expr

data RHS = AbsurdRHS
	 | RHS Expr
    deriving (Typeable, Data, Eq)

data WhereClause = NoWhere | AnyWhere [Declaration] | SomeWhere Name [Declaration]
  deriving (Typeable, Data, Eq)


-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective
	= ImportDirective
	    { importDirRange	:: !Range
	    , usingOrHiding	:: UsingOrHiding
	    , renaming		:: [Renaming]
	    , publicOpen	:: Bool	-- ^ Only for @open@. Exports the opened names from the current module.
	    }
    deriving (Typeable, Data, Eq)

defaultImportDir :: ImportDirective
defaultImportDir = ImportDirective noRange (Hiding []) [] False

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

data Renaming = Renaming { renFrom    :: ImportedName
                           -- ^ Rename from this name.
                         , renTo      :: Name
                           -- ^ To this one.
                         , renToRange :: Range
                           -- ^ The range of the \"to\" keyword. Retained
                           --   for highlighting purposes.
                         }
    deriving (Eq, Typeable, Data)

data AsName = AsName { asName  :: Name
                       -- ^ The \"as\" name.
                     , asRange :: Range
                       -- ^ The range of the \"as\" keyword. Retained
                       --   for highlighting purposes.
                     }
    deriving (Eq, Typeable, Data)

{--------------------------------------------------------------------------
    Declarations
 --------------------------------------------------------------------------}

-- | Just type signatures.
type TypeSignature   = Declaration

-- | A constructor or field declaration is just a type signature.
type Constructor = TypeSignature
type Field	 = TypeSignature

{-| The representation type of a declaration. The comments indicate
    which type in the intended family the constructor targets.
-}
data Declaration
	= TypeSig Name Expr
        | Field Hiding Name Expr
	| FunClause LHS RHS WhereClause
	| Data        !Range Induction Name [TypedBindings] Expr [Constructor]
	| Record      !Range Name (Maybe Name) [TypedBindings] Expr [Declaration]
          -- ^ The optional name is a name for the record constructor.
	| Infix Fixity [Name]
	| Mutual      !Range [Declaration]
	| Abstract    !Range [Declaration]
	| Private     !Range [Declaration]
	| Postulate   !Range [TypeSignature]
	| Primitive   !Range [TypeSignature]
	| Open        !Range QName ImportDirective
	| Import      !Range QName (Maybe AsName) OpenShortHand ImportDirective
	| ModuleMacro !Range  Name [TypedBindings] Expr OpenShortHand ImportDirective
	| Module      !Range QName [TypedBindings] [Declaration]
	| Pragma      Pragma
    deriving (Eq, Typeable, Data)

data OpenShortHand = DoOpen | DontOpen
    deriving (Eq, Typeable, Data, Show)

-- Pragmas ----------------------------------------------------------------

data Pragma = OptionsPragma     !Range [String]
	    | BuiltinPragma     !Range String Expr
            | CompiledDataPragma !Range QName String [String]
            | CompiledTypePragma !Range QName String
            | CompiledPragma    !Range QName String
            | ImportPragma      !Range String
            | ImpossiblePragma !Range
    deriving (Eq, Typeable, Data)

---------------------------------------------------------------------------

-- | Modules: Top-level pragmas plus other top-level declarations.

type Module = ([Pragma], [Declaration])

-- | Computes the top-level module name.
--
-- Precondition: The 'Module' has to be well-formed.

topLevelModuleName :: Module -> TopLevelModuleName
topLevelModuleName (_, []) = __IMPOSSIBLE__
topLevelModuleName (_, ds) = case last ds of
  Module _ n _ _ -> toTopLevelModuleName n
  _              -> __IMPOSSIBLE__

{--------------------------------------------------------------------------
    Views
 --------------------------------------------------------------------------}

-- | The 'Expr' is not an application.
data AppView = AppView Expr [NamedArg Expr]

appView :: Expr -> AppView
appView (App r e1 e2) = vApp (appView e1) e2
    where
	vApp (AppView e es) arg = AppView e (es ++ [arg])
appView (RawApp _ (e:es)) = AppView e $ map arg es
    where
	arg (HiddenArg _ e) = Arg Hidden e
	arg e		    = Arg NotHidden (unnamed e)
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
	    RawApp r _		-> r
	    OpApp r _ _		-> r
            WithApp r _ _       -> r
	    Lam r _ _		-> r
            AbsurdLam r _       -> r
	    Fun r _ _		-> r
	    Pi b e		-> fuseRange b e
	    Set r		-> r
	    Prop r		-> r
	    SetN r _		-> r
	    Let r _ _		-> r
	    Paren r _		-> r
	    As r _ _		-> r
	    Dot r _		-> r
	    Absurd r		-> r
	    HiddenArg r _	-> r
	    Rec r _		-> r
            ETel tel            -> getRange tel

-- instance HasRange Telescope where
--     getRange (TeleBind bs) = getRange bs
--     getRange (TeleFun x y) = fuseRange x y

instance HasRange TypedBindings where
    getRange (TypedBindings r _ _) = r

instance HasRange TypedBinding where
    getRange (TBind r _ _) = r
    getRange (TNoBind e)   = getRange e

instance HasRange LamBinding where
    getRange (DomainFree _ x)	= getRange x
    getRange (DomainFull b)	= getRange b

instance HasRange BoundName where
  getRange = getRange . boundName

instance HasRange WhereClause where
  getRange  NoWhere	    = noRange
  getRange (AnyWhere ds)    = getRange ds
  getRange (SomeWhere _ ds) = getRange ds

instance HasRange Declaration where
    getRange (TypeSig x t)		= fuseRange x t
    getRange (Field _ x t)              = fuseRange x t
    getRange (FunClause lhs rhs wh)	= fuseRange lhs rhs `fuseRange` wh
    getRange (Data r _ _ _ _ _)		= r
    getRange (Record r _ _ _ _ _)	= r
    getRange (Mutual r _)		= r
    getRange (Abstract r _)		= r
    getRange (Open r _ _)		= r
    getRange (ModuleMacro r _ _ _ _ _)	= r
    getRange (Import r _ _ _ _)		= r
    getRange (Private r _)		= r
    getRange (Postulate r _)		= r
    getRange (Primitive r _)		= r
    getRange (Module r _ _ _)		= r
    getRange (Infix f _)		= getRange f
    getRange (Pragma p)			= getRange p

instance HasRange LHS where
  getRange (LHS p ps eqns ws) = fuseRange p (fuseRange ps (eqns ++ ws))
  getRange (Ellipsis r _ _ _) = r

instance HasRange RHS where
    getRange AbsurdRHS = noRange
    getRange (RHS e)   = getRange e

instance HasRange Pragma where
    getRange (OptionsPragma r _)          = r
    getRange (BuiltinPragma r _ _)        = r
    getRange (CompiledDataPragma r _ _ _) = r
    getRange (CompiledTypePragma r _ _)   = r
    getRange (CompiledPragma r _ _)       = r
    getRange (ImportPragma r _)           = r
    getRange (ImpossiblePragma r)         = r

instance HasRange UsingOrHiding where
    getRange (Using xs)	    = getRange xs
    getRange (Hiding xs)    = getRange xs

instance HasRange ImportDirective where
    getRange = importDirRange

instance HasRange ImportedName where
    getRange (ImportedName x)	= getRange x
    getRange (ImportedModule x)	= getRange x

instance HasRange Renaming where
  getRange r = getRange (renFrom r, renTo r)

instance HasRange AsName where
  getRange a = getRange (asRange a, asName a)

instance HasRange Pattern where
    getRange (IdentP x)		= getRange x
    getRange (AppP p q)		= fuseRange p q
    getRange (OpAppP r _ _)	= r
    getRange (RawAppP r _)	= r
    getRange (ParenP r _)	= r
    getRange (WildP r)		= r
    getRange (AsP r _ _)	= r
    getRange (AbsurdP r)	= r
    getRange (LitP l)		= getRange l
    getRange (HiddenP r _)	= r
    getRange (DotP r _)		= r

