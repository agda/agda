{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE FlexibleInstances  #-}

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
  , LamBinding
  , LamBinding'(..)
  , TypedBindings
  , TypedBindings'(..)
  , TypedBinding
  , TypedBinding'(..)
  , RecordAssignment
  , RecordAssignments
  , FieldAssignment, FieldAssignment'(..), nameFieldA, exprFieldA
  , ModuleAssignment(..)
  , ColoredTypedBinding(..)
  , BoundName(..), mkBoundName_, mkBoundName
  , Telescope -- (..)
  , countTelVars
    -- * Declarations
  , Declaration(..)
  , ModuleApplication(..)
  , TypeSignature
  , TypeSignatureOrInstanceBlock
  , ImportDirective(..), Using(..), ImportedName(..)
  , Renaming(..), AsName(..)
  , defaultImportDir
  , isDefaultImportDir
  , OpenShortHand(..), RewriteEqn, WithExpr
  , LHS(..), Pattern(..), LHSCore(..)
  , RHS, RHS'(..), WhereClause, WhereClause'(..)
  , Pragma(..)
  , Module
  , ThingWithFixity(..)
  , topLevelModuleName
    -- * Pattern tools
  , patternNames, patternQNames
    -- * Lenses
  , mapLhsOriginalPattern
    -- * Concrete instances
  , Color
  , Arg
  -- , Dom
  , NamedArg
  , ArgInfo
  )
  where

import Control.DeepSeq
import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.List
import Data.Set (Set)
import Data.Monoid

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Literal

import Agda.Syntax.Concrete.Name
import qualified Agda.Syntax.Abstract.Name as A

import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible

type Color      = Expr
type Arg a      = Common.Arg Color a
-- type Dom a      = Common.Dom Color a
type NamedArg a = Common.NamedArg Color a
type ArgInfo    = Common.ArgInfo Color

data OpApp e
  = SyntaxBindingLambda !Range [LamBinding] e
    -- ^ An abstraction inside a special syntax declaration
    --   (see Issue 358 why we introduce this).
  | Ordinary e
  deriving (Typeable, Functor, Foldable, Traversable)

fromOrdinary :: e -> OpApp e -> e
fromOrdinary d (Ordinary e) = e
fromOrdinary d _            = d

data FieldAssignment' a = FieldAssignment { _nameFieldA :: Name, _exprFieldA :: a }
  deriving (Typeable, Functor, Foldable, Traversable, Show, Eq)

type FieldAssignment = FieldAssignment' Expr

data ModuleAssignment  = ModuleAssignment
                           { _qnameModA     :: QName
                           , _exprModA      :: [Expr]
                           , _importDirModA :: ImportDirective
                           }
  deriving (Typeable)
type RecordAssignment  = Either FieldAssignment ModuleAssignment
type RecordAssignments = [RecordAssignment]

nameFieldA :: Lens' Name (FieldAssignment' a)
nameFieldA f r = f (_nameFieldA r) <&> \x -> r { _nameFieldA = x }

exprFieldA :: Lens' a (FieldAssignment' a)
exprFieldA f r = f (_exprFieldA r) <&> \x -> r { _exprFieldA = x }

qnameModA :: Lens' QName ModuleAssignment
qnameModA f r = f (_qnameModA r) <&> \x -> r { _qnameModA = x }

exprModA :: Lens' [Expr] ModuleAssignment
exprModA f r = f (_exprModA r) <&> \x -> r { _exprModA = x }

importDirModA :: Lens' ImportDirective ModuleAssignment
importDirModA f r = f (_importDirModA r) <&> \x -> r { _importDirModA = x }

-- | Concrete expressions. Should represent exactly what the user wrote.
data Expr
  = Ident QName                                -- ^ ex: @x@
  | Lit Literal                                -- ^ ex: @1@ or @\"foo\"@
  | QuestionMark !Range (Maybe Nat)            -- ^ ex: @?@ or @{! ... !}@
  | Underscore !Range (Maybe String)           -- ^ ex: @_@ or @_A_5@
  | RawApp !Range [Expr]                       -- ^ before parsing operators
  | App !Range Expr (NamedArg Expr)            -- ^ ex: @e e@, @e {e}@, or @e {x = e}@
  | OpApp !Range QName (Set A.Name)
          [NamedArg
             (MaybePlaceholder (OpApp Expr))]  -- ^ ex: @e + e@
                                               -- The 'QName' is
                                               -- possibly ambiguous,
                                               -- but it must
                                               -- correspond to one of
                                               -- the names in the
                                               -- set.
  | WithApp !Range Expr [Expr]                 -- ^ ex: @e | e1 | .. | en@
  | HiddenArg !Range (Named_ Expr)             -- ^ ex: @{e}@ or @{x=e}@
  | InstanceArg !Range (Named_ Expr)           -- ^ ex: @{{e}}@ or @{{x=e}}@
  | Lam !Range [LamBinding] Expr               -- ^ ex: @\\x {y} -> e@ or @\\(x:A){y:B} -> e@
  | AbsurdLam !Range Hiding                    -- ^ ex: @\\ ()@
  | ExtendedLam !Range [(LHS,RHS,WhereClause)] -- ^ ex: @\\ { p11 .. p1a -> e1 ; .. ; pn1 .. pnz -> en }@
  | Fun !Range Expr Expr                       -- ^ ex: @e -> e@ or @.e -> e@ (NYI: @{e} -> e@)
  | Pi Telescope Expr                          -- ^ ex: @(xs:e) -> e@ or @{xs:e} -> e@
  | Set !Range                                 -- ^ ex: @Set@
  | Prop !Range                                -- ^ ex: @Prop@
  | SetN !Range Integer                        -- ^ ex: @Set0, Set1, ..@
  | Rec !Range RecordAssignments               -- ^ ex: @record {x = a; y = b}@, or @record { x = a; M1; M2 }@
  | RecUpdate !Range Expr [FieldAssignment]    -- ^ ex: @record e {x = a; y = b}@
  | Let !Range [Declaration] Expr              -- ^ ex: @let Ds in e@
  | Paren !Range Expr                          -- ^ ex: @(e)@
  | Absurd !Range                              -- ^ ex: @()@ or @{}@, only in patterns
  | As !Range Name Expr                        -- ^ ex: @x\@p@, only in patterns
  | Dot !Range Expr                            -- ^ ex: @.p@, only in patterns
  | ETel Telescope                             -- ^ only used for printing telescopes
  | QuoteGoal !Range Name Expr                 -- ^ ex: @quoteGoal x in e@
  | QuoteContext !Range                        -- ^ ex: @quoteContext@
  | Quote !Range                               -- ^ ex: @quote@, should be applied to a name
  | QuoteTerm !Range                           -- ^ ex: @quoteTerm@, should be applied to a term
  | Tactic !Range Expr [Expr]                  -- ^ @tactic solve | subgoal1 | .. | subgoalN@
  | Unquote !Range                             -- ^ ex: @unquote@, should be applied to a term of type @Term@
  | DontCare Expr                              -- ^ to print irrelevant things
  | Equal !Range Expr Expr                     -- ^ ex: @a = b@, used internally in the parser
  deriving (Typeable)

-- | Concrete patterns. No literals in patterns at the moment.
data Pattern
  = IdentP QName                            -- ^ @c@ or @x@
  | QuoteP !Range                           -- ^ @quote@
  | AppP Pattern (NamedArg Pattern)         -- ^ @p p'@ or @p {x = p'}@
  | RawAppP !Range [Pattern]                -- ^ @p1..pn@ before parsing operators
  | OpAppP !Range QName (Set A.Name)
           [NamedArg Pattern]               -- ^ eg: @p => p'@ for operator @_=>_@
                                            -- The 'QName' is possibly
                                            -- ambiguous, but it must
                                            -- correspond to one of
                                            -- the names in the set.
  | HiddenP !Range (Named_ Pattern)         -- ^ @{p}@ or @{x = p}@
  | InstanceP !Range (Named_ Pattern)       -- ^ @{{p}}@ or @{{x = p}}@
  | ParenP !Range Pattern                   -- ^ @(p)@
  | WildP !Range                            -- ^ @_@
  | AbsurdP !Range                          -- ^ @()@
  | AsP !Range Name Pattern                 -- ^ @x\@p@ unused
  | DotP !Range Expr                        -- ^ @.e@
  | LitP Literal                            -- ^ @0@, @1@, etc.
  | RecP !Range [FieldAssignment' Pattern]  -- ^ @record {x = p; y = q}@
  deriving (Typeable)

-- | A lambda binding is either domain free or typed.
type LamBinding = LamBinding' TypedBindings
data LamBinding' a
  = DomainFree ArgInfo BoundName  -- ^ . @x@ or @{x}@ or @.x@ or @.{x}@ or @{.x}@
  | DomainFull a                  -- ^ . @(xs : e)@ or @{xs : e}@
  deriving (Typeable, Functor, Foldable, Traversable)


-- | A sequence of typed bindings with hiding information. Appears in dependent
--   function spaces, typed lambdas, and telescopes.
--
--   If the individual binding contains hiding information as well, the
--   'Hiding' in @TypedBindings@ must be the unit 'NotHidden'.

type TypedBindings = TypedBindings' TypedBinding

data TypedBindings' a = TypedBindings !Range (Arg a)
     -- ^ . @(xs : e)@ or @{xs : e}@ or something like @(x {y} _ : e)@.
  deriving (Typeable, Functor, Foldable, Traversable)

data BoundName = BName
  { boundName   :: Name
  , boundLabel  :: Name    -- ^ for implicit function types the label matters and can't be alpha-renamed
  , bnameFixity :: Fixity'
  }
  deriving (Typeable)

mkBoundName_ :: Name -> BoundName
mkBoundName_ x = mkBoundName x noFixity'

mkBoundName :: Name -> Fixity' -> BoundName
mkBoundName x f = BName x x f

-- | A typed binding.

type TypedBinding = TypedBinding' Expr

data TypedBinding' e
  = TBind !Range [WithHiding BoundName] e  -- ^ Binding @(x1 ... xn : A)@.
  | TLet  !Range [Declaration]  -- ^ Let binding @(let Ds)@ or @(open M args)@.
  deriving (Typeable, Functor, Foldable, Traversable)

-- | Color a TypeBinding. Used by Pretty.
data ColoredTypedBinding = WithColors [Color] TypedBinding

-- | A telescope is a sequence of typed bindings. Bound variables are in scope
--   in later types.
type Telescope = [TypedBindings]

countTelVars :: Telescope -> Nat
countTelVars tel =
  sum [ case unArg b of
          TBind _ xs _ -> genericLength xs
          TLet{}       -> 0
      | TypedBindings _ b <- tel ]

{-| Left hand sides can be written in infix style. For example:

    > n + suc m = suc (n + m)
    > (f ∘ g) x = f (g x)

   We use fixity information to see which name is actually defined.
-}
data LHS
  = LHS { lhsOriginalPattern :: Pattern       -- ^ @f ps@
        , lhsWithPattern     :: [Pattern]     -- ^ @| p@ (many)
        , lhsRewriteEqn      :: [RewriteEqn]  -- ^ @rewrite e@ (many)
        , lhsWithExpr        :: [WithExpr]    -- ^ @with e@ (many)
        }
    -- ^ original pattern, with-patterns, rewrite equations and with-expressions
  | Ellipsis !Range [Pattern] [RewriteEqn] [WithExpr]
    -- ^ new with-patterns, rewrite equations and with-expressions
  deriving (Typeable)

type RewriteEqn = Expr
type WithExpr   = Expr

-- | Processed (scope-checked) intermediate form of the core @f ps@ of 'LHS'.
--   Corresponds to 'lhsOriginalPattern'.
data LHSCore
  = LHSHead  { lhsDefName  :: Name                -- ^ @f@
             , lhsPats     :: [NamedArg Pattern]  -- ^ @ps@
             }
  | LHSProj  { lhsDestructor :: QName      -- ^ record projection identifier
             , lhsPatsLeft   :: [NamedArg Pattern]  -- ^ side patterns
             , lhsFocus      :: NamedArg LHSCore    -- ^ main branch
             , lhsPatsRight  :: [NamedArg Pattern]  -- ^ side patterns
             }
  deriving (Typeable)

type RHS = RHS' Expr
data RHS' e
  = AbsurdRHS -- ^ No right hand side because of absurd match.
  | RHS e
  deriving (Typeable, Functor, Foldable, Traversable)


type WhereClause = WhereClause' [Declaration]
data WhereClause' decls
  = NoWhere               -- ^ No @where@ clauses.
  | AnyWhere decls        -- ^ Ordinary @where@.
  | SomeWhere Name decls  -- ^ Named where: @module M where@.
  deriving (Typeable, Functor, Foldable, Traversable)


-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective = ImportDirective
  { importDirRange :: !Range
  , using          :: Using
  , hiding         :: [ImportedName]
  , renaming       :: [Renaming]
  , publicOpen     :: !Bool -- ^ Only for @open@. Exports the opened names from the current module.
  }
  deriving (Typeable, Eq)

data Using = UseEverything | Using [ImportedName]
  deriving (Typeable, Eq)

instance Monoid Using where
  mempty = UseEverything
  mappend UseEverything u = u
  mappend u UseEverything = u
  mappend (Using xs) (Using ys) = Using (xs ++ ys)

-- | Default is directive is @private@ (use everything, but do not export).
defaultImportDir :: ImportDirective
defaultImportDir = ImportDirective noRange UseEverything [] [] False

isDefaultImportDir :: ImportDirective -> Bool
isDefaultImportDir (ImportDirective _ UseEverything [] [] False) = True
isDefaultImportDir _                                             = False

-- | An imported name can be a module or a defined name
data ImportedName
  = ImportedModule  { importedName :: Name }
  | ImportedName    { importedName :: Name }
  deriving (Typeable, Eq, Ord)

instance Show ImportedName where
  show (ImportedModule x) = "module " ++ show x
  show (ImportedName   x) = show x

data Renaming = Renaming
  { renFrom    :: ImportedName
    -- ^ Rename from this name.
  , renTo      :: Name
    -- ^ To this one.
  , renToRange :: !Range
    -- ^ The range of the \"to\" keyword.  Retained for highlighting purposes.
  }
  deriving (Typeable, Eq)

data AsName = AsName
  { asName  :: Name
    -- ^ The \"as\" name.
  , asRange :: !Range
    -- ^ The range of the \"as\" keyword.  Retained for highlighting purposes.
  }
  deriving (Typeable, Show)

{--------------------------------------------------------------------------
    Declarations
 --------------------------------------------------------------------------}

-- | Just type signatures.
type TypeSignature = Declaration

-- | Just type signatures or instance blocks.
type TypeSignatureOrInstanceBlock = Declaration

{-| The representation type of a declaration. The comments indicate
    which type in the intended family the constructor targets.
-}

data Declaration
  = TypeSig ArgInfo Name Expr
  -- ^ Axioms and functions can be irrelevant. (Hiding should be NotHidden)
  | Field Name (Arg Expr) -- ^ Record field, can be hidden and/or irrelevant.
  | FunClause LHS RHS WhereClause
  | DataSig     !Range Induction Name [LamBinding] Expr -- ^ lone data signature in mutual block
  | Data        !Range Induction Name [LamBinding] (Maybe Expr) [TypeSignatureOrInstanceBlock]
  | RecordSig   !Range Name [LamBinding] Expr -- ^ lone record signature in mutual block
  | Record      !Range Name (Maybe (Ranged Induction)) (Maybe Bool) (Maybe (Name, IsInstance)) [LamBinding] (Maybe Expr) [Declaration]
    -- ^ The optional name is a name for the record constructor.
  | Infix Fixity [Name]
  | Syntax      Name Notation -- ^ notation declaration for a name
  | PatternSyn  !Range Name [Arg Name] Pattern
  | Mutual      !Range [Declaration]
  | Abstract    !Range [Declaration]
  | Private     !Range [Declaration]
  | InstanceB   !Range [Declaration]
  | Macro       !Range [Declaration]
  | Postulate   !Range [TypeSignatureOrInstanceBlock]
  | Primitive   !Range [TypeSignature]
  | Open        !Range QName ImportDirective
  | Import      !Range QName (Maybe AsName) !OpenShortHand ImportDirective
  | ModuleMacro !Range  Name ModuleApplication !OpenShortHand ImportDirective
  | Module      !Range QName [TypedBindings] [Declaration]
  | UnquoteDecl !Range Name Expr
  | UnquoteDef  !Range Name Expr
  | Pragma      Pragma
  deriving (Typeable)

data ModuleApplication
  = SectionApp !Range [TypedBindings] Expr
    -- ^ @tel. M args@
  | RecordModuleIFS !Range QName
    -- ^ @M {{...}}@
  deriving (Typeable)

data OpenShortHand = DoOpen | DontOpen
  deriving (Typeable, Eq, Show)

-- Pragmas ----------------------------------------------------------------

data Pragma
  = OptionsPragma          !Range [String]
  | BuiltinPragma          !Range String Expr
  | RewritePragma          !Range QName
  | CompiledDataPragma     !Range QName String [String]
  | CompiledDeclareDataPragma !Range QName String
  | CompiledTypePragma     !Range QName String
  | CompiledPragma         !Range QName String
  | CompiledExportPragma   !Range QName String
  | CompiledEpicPragma     !Range QName String
  | CompiledJSPragma       !Range QName String
  | CompiledUHCPragma !Range QName String
  | CompiledDataUHCPragma  !Range QName String [String]
  | NoSmashingPragma        !Range QName
  | StaticPragma           !Range QName
  | ImportPragma           !Range String
    -- ^ Invariant: The string must be a valid Haskell module name.
  | ImportUHCPragma        !Range String
    -- ^ same as above, but for the UHC backend
  | ImpossiblePragma       !Range
  | TerminationCheckPragma !Range (TerminationCheck Name)
  | CatchallPragma         !Range
  | DisplayPragma          !Range Pattern Expr
  deriving (Typeable)

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
    Lenses
 --------------------------------------------------------------------------}

mapLhsOriginalPattern :: (Pattern -> Pattern) -> LHS -> LHS
mapLhsOriginalPattern f lhs@Ellipsis{}                    = lhs
mapLhsOriginalPattern f lhs@LHS{ lhsOriginalPattern = p } =
  lhs { lhsOriginalPattern = f p }

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
    arg (HiddenArg   _ e) = noColorArg Hidden    Relevant e
    arg (InstanceArg _ e) = noColorArg Instance  Relevant e
    arg e                 = noColorArg NotHidden Relevant (unnamed e)
appView e = AppView e []

{--------------------------------------------------------------------------
    Patterns
 --------------------------------------------------------------------------}

-- | Get all the identifiers in a pattern in left-to-right order.
patternQNames :: Pattern -> [QName]
patternQNames p =
  case p of
    IdentP x               -> [x]
    AppP p p'              -> concatMap patternQNames [p, namedArg p']
    RawAppP _ ps           -> concatMap patternQNames  ps
    OpAppP _ x _ ps        -> x : concatMap (patternQNames . namedArg) ps
    HiddenP _ (namedPat)   -> patternQNames (namedThing namedPat)
    ParenP _ p             -> patternQNames p
    WildP _                -> []
    AbsurdP _              -> []
    AsP _ x p              -> patternQNames p
    DotP{}                 -> []
    LitP _                 -> []
    QuoteP _               -> []
    InstanceP _ (namedPat) -> patternQNames (namedThing namedPat)
    RecP _ fs              -> concatMap (patternQNames . (^. exprFieldA)) fs

-- | Get all the identifiers in a pattern in left-to-right order.
patternNames :: Pattern -> [Name]
patternNames = map unqualify . patternQNames

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

-- Lenses
------------------------------------------------------------------------

instance LensRelevance TypedBindings where
  getRelevance   (TypedBindings _ b) = getRelevance b
  mapRelevance f (TypedBindings r b) = TypedBindings r $ mapRelevance f b

instance LensHiding TypedBindings where
  getHiding   (TypedBindings _ b) = getHiding b
  mapHiding f (TypedBindings r b) = TypedBindings r $ mapHiding f b

instance LensHiding LamBinding where
  getHiding   (DomainFree ai _) = getHiding ai
  getHiding   (DomainFull a)    = getHiding a
  mapHiding f (DomainFree ai x) = DomainFree (mapHiding f ai) x
  mapHiding f (DomainFull a)    = DomainFull $ mapHiding f a

-- HasRange instances
------------------------------------------------------------------------

instance HasRange e => HasRange (OpApp e) where
  getRange e = case e of
    Ordinary e -> getRange e
    SyntaxBindingLambda r _ _ -> r

instance HasRange Expr where
  getRange e =
    case e of
      Ident x            -> getRange x
      Lit x              -> getRange x
      QuestionMark r _   -> r
      Underscore r _     -> r
      App r _ _          -> r
      RawApp r _         -> r
      OpApp r _ _ _      -> r
      WithApp r _ _      -> r
      Lam r _ _          -> r
      AbsurdLam r _      -> r
      ExtendedLam r _    -> r
      Fun r _ _          -> r
      Pi b e             -> fuseRange b e
      Set r              -> r
      Prop r             -> r
      SetN r _           -> r
      Let r _ _          -> r
      Paren r _          -> r
      As r _ _           -> r
      Dot r _            -> r
      Absurd r           -> r
      HiddenArg r _      -> r
      InstanceArg r _    -> r
      Rec r _            -> r
      RecUpdate r _ _    -> r
      ETel tel           -> getRange tel
      QuoteGoal r _ _    -> r
      QuoteContext r     -> r
      Quote r            -> r
      QuoteTerm r        -> r
      Unquote r          -> r
      Tactic r _ _       -> r
      DontCare{}         -> noRange
      Equal r _ _        -> r

-- instance HasRange Telescope where
--     getRange (TeleBind bs) = getRange bs
--     getRange (TeleFun x y) = fuseRange x y

instance HasRange TypedBindings where
  getRange (TypedBindings r _) = r

instance HasRange TypedBinding where
  getRange (TBind r _ _) = r
  getRange (TLet r _)    = r

instance HasRange LamBinding where
  getRange (DomainFree _ x) = getRange x
  getRange (DomainFull b)   = getRange b

instance HasRange BoundName where
  getRange = getRange . boundName

instance HasRange WhereClause where
  getRange  NoWhere         = noRange
  getRange (AnyWhere ds)    = getRange ds
  getRange (SomeWhere _ ds) = getRange ds

instance HasRange ModuleApplication where
  getRange (SectionApp r _ _) = r
  getRange (RecordModuleIFS r _) = r

instance HasRange a => HasRange (FieldAssignment' a) where
  getRange (FieldAssignment a b) = fuseRange a b

instance HasRange ModuleAssignment where
  getRange (ModuleAssignment a b c) = fuseRange a b `fuseRange` c

instance HasRange Declaration where
  getRange (TypeSig _ x t)         = fuseRange x t
  getRange (Field x t)             = fuseRange x t
  getRange (FunClause lhs rhs wh)  = fuseRange lhs rhs `fuseRange` wh
  getRange (DataSig r _ _ _ _)     = r
  getRange (Data r _ _ _ _ _)      = r
  getRange (RecordSig r _ _ _)     = r
  getRange (Record r _ _ _ _ _ _ _)  = r
  getRange (Mutual r _)            = r
  getRange (Abstract r _)          = r
  getRange (Open r _ _)            = r
  getRange (ModuleMacro r _ _ _ _) = r
  getRange (Import r _ _ _ _)      = r
  getRange (InstanceB r _)         = r
  getRange (Macro r _)             = r
  getRange (Private r _)           = r
  getRange (Postulate r _)         = r
  getRange (Primitive r _)         = r
  getRange (Module r _ _ _)        = r
  getRange (Infix f _)             = getRange f
  getRange (Syntax n _)            = getRange n
  getRange (PatternSyn r _ _ _)    = r
  getRange (UnquoteDecl r _ _)     = r
  getRange (UnquoteDef r _ _)      = r
  getRange (Pragma p)              = getRange p

instance HasRange LHS where
  getRange (LHS p ps eqns ws) = fuseRange p (fuseRange ps (eqns ++ ws))
  getRange (Ellipsis r _ _ _) = r

instance HasRange LHSCore where
  getRange (LHSHead f ps)              = fuseRange f ps
  getRange (LHSProj d ps1 lhscore ps2) = d `fuseRange` ps1 `fuseRange` lhscore `fuseRange` ps2

instance HasRange RHS where
  getRange AbsurdRHS = noRange
  getRange (RHS e)   = getRange e

instance HasRange Pragma where
  getRange (OptionsPragma r _)          = r
  getRange (BuiltinPragma r _ _)        = r
  getRange (RewritePragma r _)          = r
  getRange (CompiledDataPragma r _ _ _) = r
  getRange (CompiledDeclareDataPragma r _ _) = r
  getRange (CompiledTypePragma r _ _)   = r
  getRange (CompiledPragma r _ _)       = r
  getRange (CompiledExportPragma r _ _) = r
  getRange (CompiledEpicPragma r _ _)   = r
  getRange (CompiledJSPragma r _ _)     = r
  getRange (CompiledUHCPragma r _ _)    = r
  getRange (CompiledDataUHCPragma r _ _ _) = r
  getRange (NoSmashingPragma r _)        = r
  getRange (StaticPragma r _)           = r
  getRange (ImportPragma r _)           = r
  getRange (ImportUHCPragma r _)        = r
  getRange (ImpossiblePragma r)         = r
  getRange (TerminationCheckPragma r _) = r
  getRange (CatchallPragma r)           = r
  getRange (DisplayPragma r _ _)        = r

instance HasRange ImportDirective where
  getRange = importDirRange

instance HasRange ImportedName where
  getRange (ImportedName x)   = getRange x
  getRange (ImportedModule x) = getRange x

instance HasRange Renaming where
  getRange r = getRange (renFrom r, renTo r)

instance HasRange AsName where
  getRange a = getRange (asRange a, asName a)

instance HasRange Pattern where
  getRange (IdentP x)         = getRange x
  getRange (AppP p q)         = fuseRange p q
  getRange (OpAppP r _ _ _)   = r
  getRange (RawAppP r _)      = r
  getRange (ParenP r _)       = r
  getRange (WildP r)          = r
  getRange (AsP r _ _)        = r
  getRange (AbsurdP r)        = r
  getRange (LitP l)           = getRange l
  getRange (QuoteP r)         = r
  getRange (HiddenP r _)      = r
  getRange (InstanceP r _)    = r
  getRange (DotP r _)         = r
  getRange (RecP r _)         = r

-- SetRange instances
------------------------------------------------------------------------

instance SetRange TypedBindings where
  setRange r (TypedBindings _ b) = TypedBindings r b

instance SetRange Pattern where
  setRange r (IdentP x)         = IdentP (setRange r x)
  setRange r (AppP p q)         = AppP (setRange r p) (setRange r q)
  setRange r (OpAppP _ x ns ps) = OpAppP r x ns ps
  setRange r (RawAppP _ ps)     = RawAppP r ps
  setRange r (ParenP _ p)       = ParenP r p
  setRange r (WildP _)          = WildP r
  setRange r (AsP _ x p)        = AsP r (setRange r x) p
  setRange r (AbsurdP _)        = AbsurdP r
  setRange r (LitP l)           = LitP (setRange r l)
  setRange r (QuoteP _)         = QuoteP r
  setRange r (HiddenP _ p)      = HiddenP r p
  setRange r (InstanceP _ p)    = InstanceP r p
  setRange r (DotP _ e)         = DotP r e
  setRange r (RecP _ fs)        = RecP r fs

-- KillRange instances
------------------------------------------------------------------------

instance KillRange a => KillRange (FieldAssignment' a) where
  killRange (FieldAssignment a b) = killRange2 FieldAssignment a b

instance KillRange ModuleAssignment where
  killRange (ModuleAssignment a b c) = killRange3 ModuleAssignment a b c

instance KillRange AsName where
  killRange (AsName n _) = killRange1 (flip AsName noRange) n

instance KillRange BoundName where
  killRange (BName n l f) = killRange3 BName n l f

instance KillRange Declaration where
  killRange (TypeSig i n e)         = killRange2 (TypeSig i) n e
  killRange (Field n a)             = killRange2 Field n a
  killRange (FunClause l r w)       = killRange3 FunClause l r w
  killRange (DataSig _ i n l e)     = killRange4 (DataSig noRange) i n l e
  killRange (Data _ i n l e c)      = killRange4 (Data noRange i) n l e c
  killRange (RecordSig _ n l e)     = killRange3 (RecordSig noRange) n l e
  killRange (Record _ n mi mb mn k e d)= killRange7 (Record noRange) n mi mb mn k e d
  killRange (Infix f n)             = killRange2 Infix f n
  killRange (Syntax n no)           = killRange1 (\n -> Syntax n no) n
  killRange (PatternSyn _ n ns p)   = killRange3 (PatternSyn noRange) n ns p
  killRange (Mutual _ d)            = killRange1 (Mutual noRange) d
  killRange (Abstract _ d)          = killRange1 (Abstract noRange) d
  killRange (Private _ d)           = killRange1 (Private noRange) d
  killRange (InstanceB _ d)         = killRange1 (InstanceB noRange) d
  killRange (Macro _ d)             = killRange1 (Macro noRange) d
  killRange (Postulate _ t)         = killRange1 (Postulate noRange) t
  killRange (Primitive _ t)         = killRange1 (Primitive noRange) t
  killRange (Open _ q i)            = killRange2 (Open noRange) q i
  killRange (Import _ q a o i)      = killRange3 (\q a -> Import noRange q a o) q a i
  killRange (ModuleMacro _ n m o i) = killRange3 (\n m -> ModuleMacro noRange n m o) n m i
  killRange (Module _ q t d)        = killRange3 (Module noRange) q t d
  killRange (UnquoteDecl _ x t)     = killRange2 (UnquoteDecl noRange) x t
  killRange (UnquoteDef _ x t)      = killRange2 (UnquoteDef noRange) x t
  killRange (Pragma p)              = killRange1 Pragma p

instance KillRange Expr where
  killRange (Ident q)            = killRange1 Ident q
  killRange (Lit l)              = killRange1 Lit l
  killRange (QuestionMark _ n)   = QuestionMark noRange n
  killRange (Underscore _ n)     = Underscore noRange n
  killRange (RawApp _ e)         = killRange1 (RawApp noRange) e
  killRange (App _ e a)          = killRange2 (App noRange) e a
  killRange (OpApp _ n ns o)     = killRange3 (OpApp noRange) n ns o
  killRange (WithApp _ e es)     = killRange2 (WithApp noRange) e es
  killRange (HiddenArg _ n)      = killRange1 (HiddenArg noRange) n
  killRange (InstanceArg _ n)    = killRange1 (InstanceArg noRange) n
  killRange (Lam _ l e)          = killRange2 (Lam noRange) l e
  killRange (AbsurdLam _ h)      = killRange1 (AbsurdLam noRange) h
  killRange (ExtendedLam _ lrw)  = killRange1 (ExtendedLam noRange) lrw
  killRange (Fun _ e1 e2)        = killRange2 (Fun noRange) e1 e2
  killRange (Pi t e)             = killRange2 Pi t e
  killRange (Set _)              = Set noRange
  killRange (Prop _)             = Prop noRange
  killRange (SetN _ n)           = SetN noRange n
  killRange (Rec _ ne)           = killRange1 (Rec noRange) ne
  killRange (RecUpdate _ e ne)   = killRange2 (RecUpdate noRange) e ne
  killRange (Let _ d e)          = killRange2 (Let noRange) d e
  killRange (Paren _ e)          = killRange1 (Paren noRange) e
  killRange (Absurd _)           = Absurd noRange
  killRange (As _ n e)           = killRange2 (As noRange) n e
  killRange (Dot _ e)            = killRange1 (Dot noRange) e
  killRange (ETel t)             = killRange1 ETel t
  killRange (QuoteGoal _ n e)    = killRange2 (QuoteGoal noRange) n e
  killRange (QuoteContext _)     = QuoteContext noRange
  killRange (Quote _)            = Quote noRange
  killRange (QuoteTerm _)        = QuoteTerm noRange
  killRange (Unquote _)          = Unquote noRange
  killRange (Tactic _ t es)      = killRange2 (Tactic noRange) t es
  killRange (DontCare e)         = killRange1 DontCare e
  killRange (Equal _ x y)        = Equal noRange x y

instance KillRange ImportDirective where
  killRange (ImportDirective _ u h r p) =
    killRange3 (\u h r -> ImportDirective noRange u h r p) u h r

instance KillRange Using where
  killRange (Using xs) = killRange1 Using xs
  killRange UseEverything = UseEverything

instance KillRange ImportedName where
  killRange (ImportedModule n) = killRange1 ImportedModule n
  killRange (ImportedName   n) = killRange1 ImportedName   n

instance KillRange LamBinding where
  killRange (DomainFree i b) = killRange2 DomainFree i b
  killRange (DomainFull t)   = killRange1 DomainFull t

instance KillRange LHS where
  killRange (LHS p ps r w)     = killRange4 LHS p ps r w
  killRange (Ellipsis _ p r w) = killRange3 (Ellipsis noRange) p r w

instance KillRange ModuleApplication where
  killRange (SectionApp _ t e)    = killRange2 (SectionApp noRange) t e
  killRange (RecordModuleIFS _ q) = killRange1 (RecordModuleIFS noRange) q

instance KillRange e => KillRange (OpApp e) where
  killRange (SyntaxBindingLambda _ l e) = killRange2 (SyntaxBindingLambda noRange) l e
  killRange (Ordinary e)                = killRange1 Ordinary e

instance KillRange Pattern where
  killRange (IdentP q)        = killRange1 IdentP q
  killRange (AppP p n)        = killRange2 AppP p n
  killRange (RawAppP _ p)     = killRange1 (RawAppP noRange) p
  killRange (OpAppP _ n ns p) = killRange3 (OpAppP noRange) n ns p
  killRange (HiddenP _ n)     = killRange1 (HiddenP noRange) n
  killRange (InstanceP _ n)   = killRange1 (InstanceP noRange) n
  killRange (ParenP _ p)      = killRange1 (ParenP noRange) p
  killRange (WildP _)         = WildP noRange
  killRange (AbsurdP _)       = AbsurdP noRange
  killRange (AsP _ n p)       = killRange2 (AsP noRange) n p
  killRange (DotP _ e)        = killRange1 (DotP noRange) e
  killRange (LitP l)          = killRange1 LitP l
  killRange (QuoteP _)        = QuoteP noRange
  killRange (RecP _ fs)       = killRange1 (RecP noRange) fs

instance KillRange Pragma where
  killRange (OptionsPragma _ s)           = OptionsPragma noRange s
  killRange (BuiltinPragma _ s e)         = killRange1 (BuiltinPragma noRange s) e
  killRange (RewritePragma _ q)           = killRange1 (RewritePragma noRange) q
  killRange (CompiledDataPragma _ q s ss) = killRange1 (\q -> CompiledDataPragma noRange q s ss) q
  killRange (CompiledDeclareDataPragma _ q s) = killRange1 (\q -> CompiledDeclareDataPragma noRange q s) q
  killRange (CompiledTypePragma _ q s)    = killRange1 (\q -> CompiledTypePragma noRange q s) q
  killRange (CompiledPragma _ q s)        = killRange1 (\q -> CompiledPragma noRange q s) q
  killRange (CompiledExportPragma _ q s)  = killRange1 (\q -> CompiledExportPragma noRange q s) q
  killRange (CompiledEpicPragma _ q s)    = killRange1 (\q -> CompiledEpicPragma noRange q s) q
  killRange (CompiledJSPragma _ q s)      = killRange1 (\q -> CompiledJSPragma noRange q s) q
  killRange (CompiledUHCPragma _ q s)     = killRange1 (\q -> CompiledUHCPragma noRange q s) q
  killRange (CompiledDataUHCPragma _ q s ss) = killRange1 (\q -> CompiledDataUHCPragma noRange q s ss) q
  killRange (NoSmashingPragma _ q)        = killRange1 (NoSmashingPragma noRange) q
  killRange (StaticPragma _ q)            = killRange1 (StaticPragma noRange) q
  killRange (ImportPragma _ s)            = ImportPragma noRange s
  killRange (ImportUHCPragma _ s)         = ImportUHCPragma noRange s
  killRange (ImpossiblePragma _)          = ImpossiblePragma noRange
  killRange (TerminationCheckPragma _ t)  = TerminationCheckPragma noRange (killRange t)
  killRange (CatchallPragma _)            = CatchallPragma noRange
  killRange (DisplayPragma _ lhs rhs)     = killRange2 (DisplayPragma noRange) lhs rhs

instance KillRange Renaming where
  killRange (Renaming i n _) = killRange2 (\i n -> Renaming i n noRange) i n

instance KillRange RHS where
  killRange AbsurdRHS = AbsurdRHS
  killRange (RHS e)   = killRange1 RHS e

instance KillRange TypedBinding where
  killRange (TBind _ b e) = killRange2 (TBind noRange) b e
  killRange (TLet r ds)   = killRange2 TLet r ds

instance KillRange TypedBindings where
  killRange (TypedBindings _ t) = killRange1 (TypedBindings noRange) t

instance KillRange WhereClause where
  killRange NoWhere         = NoWhere
  killRange (AnyWhere d)    = killRange1 AnyWhere d
  killRange (SomeWhere n d) = killRange2 SomeWhere n d

------------------------------------------------------------------------
-- NFData instances

-- | Ranges are not forced.

instance NFData Expr where
  rnf (Ident a)          = rnf a
  rnf (Lit a)            = rnf a
  rnf (QuestionMark _ a) = rnf a
  rnf (Underscore _ a)   = rnf a
  rnf (RawApp _ a)       = rnf a
  rnf (App _ a b)        = rnf a `seq` rnf b
  rnf (OpApp _ a b c)    = rnf a `seq` rnf b `seq` rnf c
  rnf (WithApp _ a b)    = rnf a `seq` rnf b
  rnf (HiddenArg _ a)    = rnf a
  rnf (InstanceArg _ a)  = rnf a
  rnf (Lam _ a b)        = rnf a `seq` rnf b
  rnf (AbsurdLam _ a)    = rnf a
  rnf (ExtendedLam _ a)  = rnf a
  rnf (Fun _ a b)        = rnf a `seq` rnf b
  rnf (Pi a b)           = rnf a `seq` rnf b
  rnf (Set _)            = ()
  rnf (Prop _)           = ()
  rnf (SetN _ a)         = rnf a
  rnf (Rec _ a)          = rnf a
  rnf (RecUpdate _ a b)  = rnf a `seq` rnf b
  rnf (Let _ a b)        = rnf a `seq` rnf b
  rnf (Paren _ a)        = rnf a
  rnf (Absurd _)         = ()
  rnf (As _ a b)         = rnf a `seq` rnf b
  rnf (Dot _ a)          = rnf a
  rnf (ETel a)           = rnf a
  rnf (QuoteGoal _ a b)  = rnf a `seq` rnf b
  rnf (QuoteContext _)   = ()
  rnf (Quote _)          = ()
  rnf (QuoteTerm _)      = ()
  rnf (Tactic _ a b)     = rnf a `seq` rnf b
  rnf (Unquote _)        = ()
  rnf (DontCare a)       = rnf a
  rnf (Equal _ a b)      = rnf a `seq` rnf b

-- | Ranges are not forced.

instance NFData Pattern where
  rnf (IdentP a) = rnf a
  rnf (QuoteP _) = ()
  rnf (AppP a b) = rnf a `seq` rnf b
  rnf (RawAppP _ a) = rnf a
  rnf (OpAppP _ a b c) = rnf a `seq` rnf b `seq` rnf c
  rnf (HiddenP _ a) = rnf a
  rnf (InstanceP _ a) = rnf a
  rnf (ParenP _ a) = rnf a
  rnf (WildP _) = ()
  rnf (AbsurdP _) = ()
  rnf (AsP _ a b) = rnf a `seq` rnf b
  rnf (DotP _ a) = rnf a
  rnf (LitP a) = rnf a
  rnf (RecP _ a) = rnf a

-- | Ranges are not forced.

instance NFData Declaration where
  rnf (TypeSig a b c)         = rnf a `seq` rnf b `seq` rnf c
  rnf (Field a b)             = rnf a `seq` rnf b
  rnf (FunClause a b c)       = rnf a `seq` rnf b `seq` rnf c
  rnf (DataSig _ a b c d)     = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (Data _ a b c d e)      = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e
  rnf (RecordSig _ a b c)     = rnf a `seq` rnf b `seq` rnf c
  rnf (Record _ a b c d e f)  = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e `seq` rnf f
  rnf (Infix a b)             = rnf a `seq` rnf b
  rnf (Syntax a b)            = rnf a `seq` rnf b
  rnf (PatternSyn _ a b c)    = rnf a `seq` rnf b `seq` rnf c
  rnf (Mutual _ a)            = rnf a
  rnf (Abstract _ a)          = rnf a
  rnf (Private _ a)           = rnf a
  rnf (InstanceB _ a)         = rnf a
  rnf (Macro _ a)             = rnf a
  rnf (Postulate _ a)         = rnf a
  rnf (Primitive _ a)         = rnf a
  rnf (Open _ a b)            = rnf a `seq` rnf b
  rnf (Import _ a b _ c)      = rnf a `seq` rnf b `seq` rnf c
  rnf (ModuleMacro _ a b _ c) = rnf a `seq` rnf b `seq` rnf c
  rnf (Module _ a b c)        = rnf a `seq` rnf b `seq` rnf c
  rnf (UnquoteDecl _ a b)     = rnf a `seq` rnf b
  rnf (UnquoteDef _ a b)      = rnf a `seq` rnf b
  rnf (Pragma a)              = rnf a

-- | Ranges are not forced.

instance NFData Pragma where
  rnf (OptionsPragma _ a)               = rnf a
  rnf (BuiltinPragma _ a b)             = rnf a `seq` rnf b
  rnf (RewritePragma _ a)               = rnf a
  rnf (CompiledDataPragma _ a b c)      = rnf a `seq` rnf b `seq` rnf c
  rnf (CompiledDeclareDataPragma _ a b) = rnf a `seq` rnf b
  rnf (CompiledTypePragma _ a b)        = rnf a `seq` rnf b
  rnf (CompiledPragma _ a b)            = rnf a `seq` rnf b
  rnf (CompiledExportPragma _ a b)      = rnf a `seq` rnf b
  rnf (CompiledEpicPragma _ a b)        = rnf a `seq` rnf b
  rnf (CompiledJSPragma _ a b)          = rnf a `seq` rnf b
  rnf (CompiledUHCPragma _ a b)         = rnf a `seq` rnf b
  rnf (CompiledDataUHCPragma _ a b c)   = rnf a `seq` rnf b `seq` rnf c
  rnf (NoSmashingPragma _ a)            = rnf a
  rnf (StaticPragma _ a)                = rnf a
  rnf (ImportPragma _ a)                = rnf a
  rnf (ImportUHCPragma _ a)             = rnf a
  rnf (ImpossiblePragma _)              = ()
  rnf (EtaPragma _ a)                   = rnf a
  rnf (NoEtaPragma _ a)                 = rnf a
  rnf (TerminationCheckPragma _ a)      = rnf a
  rnf (CatchallPragma _)                = ()
  rnf (DisplayPragma _ a b)             = rnf a `seq` rnf b

-- | Ranges are not forced.

instance NFData a => NFData (TypedBindings' a) where
  rnf (TypedBindings _ a) = rnf a

-- | Ranges are not forced.

instance NFData Renaming where
  rnf (Renaming a b _) = rnf a `seq` rnf b

-- | Ranges are not forced.

instance NFData AsName where
  rnf (AsName a _) = rnf a

-- | Ranges are not forced.

instance NFData a => NFData (TypedBinding' a) where
  rnf (TBind _ a b) = rnf a `seq` rnf b
  rnf (TLet _ a)    = rnf a

-- | Ranges are not forced.

instance NFData ModuleApplication where
  rnf (SectionApp _ a b)    = rnf a `seq` rnf b
  rnf (RecordModuleIFS _ a) = rnf a

-- | Ranges are not forced.

instance NFData ImportDirective where
  rnf (ImportDirective _ a b c _) = rnf a `seq` rnf b `seq` rnf c

-- | Ranges are not forced.

instance NFData a => NFData (OpApp a) where
  rnf (SyntaxBindingLambda _ a b) = rnf a `seq` rnf b
  rnf (Ordinary a)                = rnf a

-- | Ranges are not forced.

instance NFData LHS where
  rnf (LHS a b c d)      = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (Ellipsis _ a b c) = rnf a `seq` rnf b `seq` rnf c

instance NFData a => NFData (FieldAssignment' a) where
  rnf (FieldAssignment a b) = rnf a `seq` rnf b

instance NFData ModuleAssignment where
  rnf (ModuleAssignment a b c) = rnf a `seq` rnf b `seq` rnf c

instance NFData a => NFData (WhereClause' a) where
  rnf NoWhere         = ()
  rnf (AnyWhere a)    = rnf a
  rnf (SomeWhere a b) = rnf a `seq` rnf b

instance NFData Using where
  rnf UseEverything = ()
  rnf (Using a)     = rnf a

instance NFData ImportedName where
  rnf (ImportedModule a) = rnf a
  rnf (ImportedName a)   = rnf a

instance NFData a => NFData (LamBinding' a) where
  rnf (DomainFree a b) = rnf a `seq` rnf b
  rnf (DomainFull a)   = rnf a

instance NFData BoundName where
  rnf (BName a b c) = rnf a `seq` rnf b `seq` rnf c

instance NFData a => NFData (RHS' a) where
  rnf AbsurdRHS = ()
  rnf (RHS a)   = rnf a
