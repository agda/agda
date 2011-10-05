{-# LANGUAGE CPP, DeriveDataTypeable, DeriveFunctor, DeriveTraversable, DeriveFoldable #-}

{-| The concrete syntax is a raw representation of the program text
    without any desugaring at all.  This is what the parser produces.
    The idea is that if we figure out how to keep the concrete syntax
    around, it can be printed exactly as the user wrote it.
-}
module Agda.Syntax.Concrete
    ( -- * Expressions
      Expr(..)
    , OpApp(..), fromOrdinary
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
    , ModuleApplication(..)
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
    , ThingWithFixity(..)
    , topLevelModuleName
    -- * Pattern tools
    , patternHead, patternNames
    )
    where

import Data.Generics (Typeable, Data)
import Data.Foldable hiding (concatMap)
import Data.Traversable
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Literal

import Agda.Syntax.Concrete.Name

import Agda.Utils.Impossible
#include "../undefined.h"

data OpApp e
        = SyntaxBindingLambda !Range [LamBinding] e -- ^ an abstraction inside a special syntax declaration (see Issue 358 why we introduce this).
        | Ordinary e
    deriving (Typeable, Data, Functor)

fromOrdinary :: e -> OpApp e -> e
fromOrdinary d (Ordinary e) = e
fromOrdinary d _            = d

-- | Concrete expressions. Should represent exactly what the user wrote.
data Expr
	= Ident QName			       -- ^ ex: @x@
	| Lit Literal			       -- ^ ex: @1@ or @\"foo\"@
	| QuestionMark !Range (Maybe Nat)      -- ^ ex: @?@ or @{! ... !}@
	| Underscore !Range (Maybe Nat)	       -- ^ ex: @_@
	| RawApp !Range [Expr]		       -- ^ before parsing operators
	| App !Range Expr (NamedArg Expr)      -- ^ ex: @e e@, @e {e}@, or @e {x = e}@
	| OpApp !Range Name [OpApp Expr]       -- ^ ex: @e + e@
        | WithApp !Range Expr [Expr]           -- ^ ex: @e | e1 | .. | en@
	| HiddenArg !Range (Named String Expr) -- ^ ex: @{e}@ or @{x=e}@
	| InstanceArg !Range (Named String Expr) -- ^ ex: @{{e}}@ or @{{x=e}}@
	| Lam !Range [LamBinding] Expr	       -- ^ ex: @\\x {y} -> e@ or @\\(x:A){y:B} -> e@
        | AbsurdLam !Range Hiding              -- ^ ex: @\\ ()@
        | ExtendedLam !Range [(LHS,RHS,WhereClause)]       -- ^ ex: @\\ { p11 .. p1a -> e1 ; .. ; pn1 .. pnz -> en }@
	| Fun !Range Expr Expr                 -- ^ ex: @e -> e@ or @.e -> e@ (NYI: @{e} -> e@)
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
        | QuoteGoal !Range Name Expr           -- ^ ex: @quoteGoal x in e@
        | Quote !Range                         -- ^ ex: @quote@, should be applied to a name
        | QuoteTerm !Range                     -- ^ ex: @quoteTerm@, should be applied to a term
        | Unquote !Range                       -- ^ ex: @unquote@, should be applied to a term of type @Term@
        | DontCare Expr                        -- ^ to print irrelevant things
    deriving (Typeable, Data)


-- | Concrete patterns. No literals in patterns at the moment.
data Pattern
	= IdentP QName
	| AppP Pattern (NamedArg Pattern)
	| RawAppP !Range [Pattern]
	| OpAppP !Range Name [Pattern]
	| HiddenP !Range (Named String Pattern)
	| InstanceP !Range (Named String Pattern)
	| ParenP !Range Pattern
	| WildP !Range
	| AbsurdP !Range
	| AsP !Range Name Pattern
	| DotP !Range Expr
	| LitP Literal
    deriving (Typeable, Data)


-- | A lambda binding is either domain free or typed.
data LamBinding
	= DomainFree Hiding Relevance BoundName -- ^ . @x@ or @{x}@ or @.x@ or @.{x}@ or @{.x}@
	| DomainFull TypedBindings              -- ^ . @(xs : e)@ or @{xs : e}@
    deriving (Typeable, Data)


-- | A sequence of typed bindings with hiding information. Appears in dependent
--   function spaces, typed lambdas, and telescopes.
data TypedBindings = TypedBindings !Range (Arg TypedBinding)
	-- ^ . @(xs : e)@ or @{xs : e}@
    deriving (Typeable, Data)


data BoundName = BName { boundName   :: Name
                       , bnameFixity :: Fixity'
                       }
    deriving (Typeable, Data)

mkBoundName_ :: Name -> BoundName
mkBoundName_ x = BName x defaultFixity'

-- | A typed binding.
data TypedBinding
	= TBind !Range [BoundName] Expr   -- Binding @x1,..,xn:A@
	| TNoBind Expr		    -- No binding @A@, equivalent to @_ : A@.
    deriving (Typeable, Data)


-- | A telescope is a sequence of typed bindings. Bound variables are in scope
--   in later types.
type Telescope = [TypedBindings]

{-| Left hand sides can be written in infix style. For example:

    > n + suc m = suc (n + m)
    > (f ∘ g) x = f (g x)

   We use fixity information to see which name is actually defined.
-}
data LHS = LHS { lhsOriginalPattern :: Pattern
               , lhsWithPattern     :: [Pattern]
               , lhsRewriteEqn      :: [RewriteEqn]
               , lhsWithExpr        :: [WithExpr]
               }
         -- ^ original pattern, with-patterns, rewrite equations and with-expressions
         | Ellipsis Range [Pattern] [RewriteEqn] [WithExpr]
         -- ^ new with-patterns, rewrite equations and with-expressions
  deriving (Typeable, Data)

type RewriteEqn = Expr
type WithExpr   = Expr

data RHS = AbsurdRHS
	 | RHS Expr
    deriving (Typeable, Data)

data WhereClause = NoWhere | AnyWhere [Declaration] | SomeWhere Name [Declaration]
  deriving (Typeable, Data)


-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective
	= ImportDirective
	    { importDirRange	:: !Range
	    , usingOrHiding	:: UsingOrHiding
	    , renaming		:: [Renaming]
	    , publicOpen	:: Bool	-- ^ Only for @open@. Exports the opened names from the current module.
	    }
    deriving (Typeable, Data)

defaultImportDir :: ImportDirective
defaultImportDir = ImportDirective noRange (Hiding []) [] False

data UsingOrHiding
	= Hiding [ImportedName]
	| Using  [ImportedName]
    deriving (Typeable, Data)

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
    deriving (Typeable, Data)

data AsName = AsName { asName  :: Name
                       -- ^ The \"as\" name.
                     , asRange :: Range
                       -- ^ The range of the \"as\" keyword. Retained
                       --   for highlighting purposes.
                     }
    deriving (Typeable, Data, Show)

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
	= TypeSig Relevance Name Expr -- ^ Axioms and functions can be irrelevant.
        | Field Name (Arg Expr) -- ^ Record field, can be hidden and/or irrelevant.
	| FunClause LHS RHS WhereClause
	| DataSig     !Range Induction Name [LamBinding] Expr -- ^ lone data signature in mutual block
	| Data        !Range Induction Name [LamBinding] (Maybe Expr) [Constructor]
	| RecordSig   !Range Name [LamBinding] Expr -- ^ lone record signature in mutual block
	| Record      !Range Name (Maybe Name) [LamBinding] (Maybe Expr) [Declaration]
          -- ^ The optional name is a name for the record constructor.
	| Infix Fixity [Name]
        | Syntax      Name Notation -- ^ notation declaration for a name
	| Mutual      !Range [Declaration]
	| Abstract    !Range [Declaration]
	| Private     !Range [Declaration]
	| Postulate   !Range [TypeSignature]
	| Primitive   !Range [TypeSignature]
	| Open        !Range QName ImportDirective
	| Import      !Range QName (Maybe AsName) OpenShortHand ImportDirective
	| ModuleMacro !Range  Name ModuleApplication OpenShortHand ImportDirective
	| Module      !Range QName [TypedBindings] [Declaration]
	| Pragma      Pragma
    deriving (Typeable, Data)

data ModuleApplication = SectionApp Range [TypedBindings] Expr
                       | RecordModuleIFS Range QName
    deriving (Typeable, Data)

data OpenShortHand = DoOpen | DontOpen
    deriving (Typeable, Data, Show)

-- Pragmas ----------------------------------------------------------------

data Pragma = OptionsPragma     !Range [String]
	    | BuiltinPragma     !Range String Expr
            | CompiledDataPragma !Range QName String [String]
            | CompiledTypePragma !Range QName String
            | CompiledPragma    !Range QName String
            | CompiledEpicPragma !Range QName String
            | CompiledJSPragma  !Range QName String
            | StaticPragma      !Range QName
            | ImportPragma      !Range String
              -- ^ Invariant: The string must be a valid Haskell
              -- module name.
            | ImpossiblePragma !Range
            | EtaPragma !Range QName
    deriving (Typeable, Data)

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
	arg (HiddenArg _ e) = Arg Hidden    Relevant e
	arg e		    = Arg NotHidden Relevant (unnamed e)
appView e = AppView e []

{--------------------------------------------------------------------------
    Patterns
 --------------------------------------------------------------------------}

-- | Get the leftmost symbol in a pattern.
patternHead :: Pattern -> Maybe Name
patternHead p =
  case p of
    IdentP x             -> return $ unqualify x
    AppP p p'            -> patternHead p
    RawAppP _ []         -> __IMPOSSIBLE__
    RawAppP _ (p:_)      -> patternHead p
    OpAppP _ name ps     -> return $ name
    HiddenP _ (namedPat) -> patternHead (namedThing namedPat)
    ParenP _ p           -> patternHead p
    WildP _              -> Nothing
    AbsurdP _            -> Nothing
    AsP _ x p            -> patternHead p
    DotP{}               -> Nothing
    LitP (LitQName _ x)  -> Nothing -- return $ unqualify x -- does not compile
    LitP _               -> Nothing
    InstanceP _ (namedPat) -> patternHead (namedThing namedPat)


-- | Get all the identifiers in a pattern in left-to-right order.
patternNames :: Pattern -> [Name]
patternNames p =
  case p of
    IdentP x             -> [unqualify x]
    AppP p p'            -> concatMap patternNames [p, namedThing $ unArg p']
    RawAppP _ ps         -> concatMap patternNames  ps
    OpAppP _ name ps     -> name : concatMap patternNames ps
    HiddenP _ (namedPat) -> patternNames (namedThing namedPat)
    ParenP _ p           -> patternNames p
    WildP _              -> []
    AbsurdP _            -> []
    AsP _ x p            -> patternNames p
    DotP{}               -> []
    LitP _               -> []
    InstanceP _ (namedPat) -> patternNames (namedThing namedPat)

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance HasRange e => HasRange (OpApp e) where
    getRange e = case e of
        Ordinary e -> getRange e
        SyntaxBindingLambda r _ _ -> r

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
            ExtendedLam r _       -> r
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
	    InstanceArg r _	-> r
	    Rec r _		-> r
            ETel tel            -> getRange tel
            QuoteGoal r _ _     -> r
            Quote r             -> r
            QuoteTerm r         -> r
            Unquote r           -> r
            DontCare{}          -> noRange

-- instance HasRange Telescope where
--     getRange (TeleBind bs) = getRange bs
--     getRange (TeleFun x y) = fuseRange x y

instance HasRange TypedBindings where
    getRange (TypedBindings r _) = r

instance HasRange TypedBinding where
    getRange (TBind r _ _) = r
    getRange (TNoBind e)   = getRange e

instance HasRange LamBinding where
    getRange (DomainFree _ _ x)	= getRange x
    getRange (DomainFull b)	= getRange b

instance HasRange BoundName where
  getRange = getRange . boundName

instance HasRange WhereClause where
  getRange  NoWhere	    = noRange
  getRange (AnyWhere ds)    = getRange ds
  getRange (SomeWhere _ ds) = getRange ds

instance HasRange ModuleApplication where
  getRange (SectionApp r _ _) = r
  getRange (RecordModuleIFS r _) = r

instance HasRange Declaration where
    getRange (TypeSig _ x t)	       = fuseRange x t
    getRange (Field x t)               = fuseRange x t
    getRange (FunClause lhs rhs wh)    = fuseRange lhs rhs `fuseRange` wh
    getRange (DataSig r _ _ _ _)       = r
    getRange (Data r _ _ _ _ _)	       = r
    getRange (RecordSig r _ _ _)       = r
    getRange (Record r _ _ _ _ _)      = r
    getRange (Mutual r _)	       = r
    getRange (Abstract r _)	       = r
    getRange (Open r _ _)	       = r
    getRange (ModuleMacro r _ _ _ _)   = r
    getRange (Import r _ _ _ _)	       = r
    getRange (Private r _)	       = r
    getRange (Postulate r _)	       = r
    getRange (Primitive r _)	       = r
    getRange (Module r _ _ _)	       = r
    getRange (Infix f _)	       = getRange f
    getRange (Syntax n _)              = getRange n
    getRange (Pragma p)		       = getRange p

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
    getRange (CompiledEpicPragma r _ _)   = r
    getRange (CompiledJSPragma r _ _)     = r
    getRange (StaticPragma r _)           = r
    getRange (ImportPragma r _)           = r
    getRange (ImpossiblePragma r)         = r
    getRange (EtaPragma r _)              = r

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
    getRange (InstanceP r _)	= r
    getRange (DotP r _)		= r
