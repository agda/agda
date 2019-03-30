{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}

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
  , isSingleIdentifierP, removeSingletonRawAppP
    -- * Bindings
  , LamBinding
  , LamBinding'(..)
  , TypedBinding
  , TypedBinding'(..)
  , RecordAssignment
  , RecordAssignments
  , FieldAssignment, FieldAssignment'(..), nameFieldA, exprFieldA
  , ModuleAssignment(..)
  , BoundName(..), mkBoundName_, mkBoundName
  , Telescope -- (..)
  , countTelVars
  , lamBindingsToTelescope
  , makePi
    -- * Declarations
  , Declaration(..)
  , ModuleApplication(..)
  , TypeSignature
  , TypeSignatureOrInstanceBlock
  , ImportDirective, Using, ImportedName
  , Renaming
  , AsName'(..), AsName
  , OpenShortHand(..), RewriteEqn, WithExpr
  , LHS(..), Pattern(..), LHSCore(..)
  , LamClause(..)
  , RHS, RHS'(..), WhereClause, WhereClause'(..), ExprWhere(..)
  , DoStmt(..)
  , Pragma(..)
  , Module
  , ThingWithFixity(..)
  , HoleContent, HoleContent'(..)
  , topLevelModuleName
  , spanAllowedBeforeModule
  )
  where

import Prelude hiding (null)

import Control.DeepSeq
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.List hiding (null)
import Data.Set (Set)
import Data.Monoid

import Data.Data (Data)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Literal

import Agda.Syntax.Concrete.Name
import qualified Agda.Syntax.Abstract.Name as A

import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.Lens
import Agda.Utils.Null

#include "undefined.h"
import Agda.Utils.Impossible

data OpApp e
  = SyntaxBindingLambda Range [LamBinding] e
    -- ^ An abstraction inside a special syntax declaration
    --   (see Issue 358 why we introduce this).
  | Ordinary e
  deriving (Data, Functor, Foldable, Traversable)

fromOrdinary :: e -> OpApp e -> e
fromOrdinary d (Ordinary e) = e
fromOrdinary d _            = d

data FieldAssignment' a = FieldAssignment { _nameFieldA :: Name, _exprFieldA :: a }
  deriving (Data, Functor, Foldable, Traversable, Show, Eq)

type FieldAssignment = FieldAssignment' Expr

data ModuleAssignment  = ModuleAssignment
                           { _qnameModA     :: QName
                           , _exprModA      :: [Expr]
                           , _importDirModA :: ImportDirective
                           }
  deriving Data
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
  | QuestionMark Range (Maybe Nat)             -- ^ ex: @?@ or @{! ... !}@
  | Underscore Range (Maybe String)            -- ^ ex: @_@ or @_A_5@
  | RawApp Range [Expr]                        -- ^ before parsing operators
  | App Range Expr (NamedArg Expr)             -- ^ ex: @e e@, @e {e}@, or @e {x = e}@
  | OpApp Range QName (Set A.Name)
          [NamedArg
             (MaybePlaceholder (OpApp Expr))]  -- ^ ex: @e + e@
                                               -- The 'QName' is
                                               -- possibly ambiguous,
                                               -- but it must
                                               -- correspond to one of
                                               -- the names in the
                                               -- set.
  | WithApp Range Expr [Expr]                  -- ^ ex: @e | e1 | .. | en@
  | HiddenArg Range (Named_ Expr)              -- ^ ex: @{e}@ or @{x=e}@
  | InstanceArg Range (Named_ Expr)            -- ^ ex: @{{e}}@ or @{{x=e}}@
  | Lam Range [LamBinding] Expr                -- ^ ex: @\\x {y} -> e@ or @\\(x:A){y:B} -> e@
  | AbsurdLam Range Hiding                     -- ^ ex: @\\ ()@
  | ExtendedLam Range [LamClause]              -- ^ ex: @\\ { p11 .. p1a -> e1 ; .. ; pn1 .. pnz -> en }@
  | Fun Range (Arg Expr) Expr                  -- ^ ex: @e -> e@ or @.e -> e@ (NYI: @{e} -> e@)
  | Pi Telescope Expr                          -- ^ ex: @(xs:e) -> e@ or @{xs:e} -> e@
  | Set Range                                  -- ^ ex: @Set@
  | Prop Range                                 -- ^ ex: @Prop@
  | SetN Range Integer                         -- ^ ex: @Set0, Set1, ..@
  | PropN Range Integer                        -- ^ ex: @Prop0, Prop1, ..@
  | Rec Range RecordAssignments                -- ^ ex: @record {x = a; y = b}@, or @record { x = a; M1; M2 }@
  | RecUpdate Range Expr [FieldAssignment]     -- ^ ex: @record e {x = a; y = b}@
  | Let Range [Declaration] (Maybe Expr)       -- ^ ex: @let Ds in e@, missing body when parsing do-notation let
  | Paren Range Expr                           -- ^ ex: @(e)@
  | IdiomBrackets Range Expr                   -- ^ ex: @(| e |)@
  | DoBlock Range [DoStmt]                     -- ^ ex: @do x <- m1; m2@
  | Absurd Range                               -- ^ ex: @()@ or @{}@, only in patterns
  | As Range Name Expr                         -- ^ ex: @x\@p@, only in patterns
  | Dot Range Expr                             -- ^ ex: @.p@, only in patterns
  | ETel Telescope                             -- ^ only used for printing telescopes
  | QuoteGoal Range Name Expr                  -- ^ ex: @quoteGoal x in e@
  | QuoteContext Range                         -- ^ ex: @quoteContext@
  | Quote Range                                -- ^ ex: @quote@, should be applied to a name
  | QuoteTerm Range                            -- ^ ex: @quoteTerm@, should be applied to a term
  | Tactic Range Expr [Expr]                   -- ^ @tactic solve | subgoal1 | .. | subgoalN@
  | Unquote Range                              -- ^ ex: @unquote@, should be applied to a term of type @Term@
  | DontCare Expr                              -- ^ to print irrelevant things
  | Equal Range Expr Expr                      -- ^ ex: @a = b@, used internally in the parser
  | Ellipsis Range                             -- ^ @...@, used internally to parse patterns.
  | Generalized Expr
  deriving Data

-- | Concrete patterns. No literals in patterns at the moment.
data Pattern
  = IdentP QName                           -- ^ @c@ or @x@
  | QuoteP Range                           -- ^ @quote@
  | AppP Pattern (NamedArg Pattern)        -- ^ @p p'@ or @p {x = p'}@
  | RawAppP Range [Pattern]                -- ^ @p1..pn@ before parsing operators
  | OpAppP Range QName (Set A.Name)
           [NamedArg Pattern]              -- ^ eg: @p => p'@ for operator @_=>_@
                                           -- The 'QName' is possibly
                                           -- ambiguous, but it must
                                           -- correspond to one of
                                           -- the names in the set.
  | HiddenP Range (Named_ Pattern)         -- ^ @{p}@ or @{x = p}@
  | InstanceP Range (Named_ Pattern)       -- ^ @{{p}}@ or @{{x = p}}@
  | ParenP Range Pattern                   -- ^ @(p)@
  | WildP Range                            -- ^ @_@
  | AbsurdP Range                          -- ^ @()@
  | AsP Range Name Pattern                 -- ^ @x\@p@ unused
  | DotP Range Expr                        -- ^ @.e@
  | LitP Literal                           -- ^ @0@, @1@, etc.
  | RecP Range [FieldAssignment' Pattern]  -- ^ @record {x = p; y = q}@
  | EqualP Range [(Expr,Expr)]             -- ^ @i = i1@ i.e. cubical face lattice generator
  | EllipsisP Range                        -- ^ @...@, only as left-most pattern.
  | WithP Range Pattern                    -- ^ @| p@, for with-patterns.
  deriving Data

data DoStmt
  = DoBind Range Pattern Expr [LamClause]   -- ^ @p ← e where cs@
  | DoThen Expr
  | DoLet Range [Declaration]
  deriving Data

-- | A lambda binding is either domain free or typed.
type LamBinding = LamBinding' TypedBinding
data LamBinding' a
  = DomainFree (NamedArg BoundName) -- ^ . @x@ or @{x}@ or @.x@ or @.{x}@ or @{.x}@
  | DomainFull a                    -- ^ . @(xs : e)@ or @{xs : e}@
  deriving (Data, Functor, Foldable, Traversable)

data BoundName = BName
  { boundName   :: Name
  , bnameFixity :: Fixity'
  }
  deriving (Data, Eq, Show)

mkBoundName_ :: Name -> BoundName
mkBoundName_ x = mkBoundName x noFixity'

mkBoundName :: Name -> Fixity' -> BoundName
mkBoundName x f = BName x f

-- | A typed binding.

type TypedBinding = TypedBinding' Expr

data TypedBinding' e
  = TBind Range [NamedArg BoundName] e  -- ^ Binding @(x1 ... xn : A)@.
  | TLet  Range [Declaration]           -- ^ Let binding @(let Ds)@ or @(open M args)@.
  deriving (Data, Functor, Foldable, Traversable)

-- | A telescope is a sequence of typed bindings. Bound variables are in scope
--   in later types.
type Telescope = [TypedBinding]

countTelVars :: Telescope -> Nat
countTelVars tel =
  sum [ case b of
          TBind _ xs _ -> genericLength xs
          TLet{}       -> 0
      | b <- tel ]

-- | We can try to get a @Telescope@ from a @[LamBinding]@.
--   If we have a type annotation already, we're happy.
--   Otherwise we manufacture a binder with an underscore for the type.
lamBindingsToTelescope :: Range -> [LamBinding] -> Telescope
lamBindingsToTelescope r = map $ \case
  DomainFull ty -> ty
  DomainFree nm -> TBind r [nm] $ Underscore r Nothing

-- | Smart constructor for @Pi@: check whether the @Telescope@ is empty

makePi :: Telescope -> Expr -> Expr
makePi [] e = e
makePi bs e = Pi bs e

{-| Left hand sides can be written in infix style. For example:

    > n + suc m = suc (n + m)
    > (f ∘ g) x = f (g x)

   We use fixity information to see which name is actually defined.
-}
data LHS = LHS
  { lhsOriginalPattern :: Pattern       -- ^ e.g. @f ps | wps@
  , lhsRewriteEqn      :: [RewriteEqn]  -- ^ @rewrite e@ (many)
  , lhsWithExpr        :: [WithExpr]    -- ^ @with e@ (many)
  } -- ^ Original pattern (including with-patterns), rewrite equations and with-expressions.
  deriving Data

type RewriteEqn = Expr
type WithExpr   = Expr

-- | Processed (operator-parsed) intermediate form of the core @f ps@ of 'LHS'.
--   Corresponds to 'lhsOriginalPattern'.
data LHSCore
  = LHSHead  { lhsDefName      :: QName               -- ^ @f@
             , lhsPats         :: [NamedArg Pattern]  -- ^ @ps@
             }
  | LHSProj  { lhsDestructor   :: QName               -- ^ Record projection.
             , lhsPatsLeft     :: [NamedArg Pattern]  -- ^ Patterns for record indices (currently none).
             , lhsFocus        :: NamedArg LHSCore    -- ^ Main argument.
             , lhsPats         :: [NamedArg Pattern]  -- ^ More application patterns.
             }
  | LHSWith  { lhsHead         :: LHSCore
             , lhsWithPatterns :: [Pattern]          -- ^ Non-empty; at least one @(| p)@.
             , lhsPats         :: [NamedArg Pattern] -- ^ More application patterns.
             }

type RHS = RHS' Expr
data RHS' e
  = AbsurdRHS -- ^ No right hand side because of absurd match.
  | RHS e
  deriving (Data, Functor, Foldable, Traversable)


type WhereClause = WhereClause' [Declaration]
data WhereClause' decls
  = NoWhere               -- ^ No @where@ clauses.
  | AnyWhere decls        -- ^ Ordinary @where@.
  | SomeWhere Name Access decls
    -- ^ Named where: @module M where@.
    --   The 'Access' flag applies to the 'Name' (not the module contents!)
    --   and is propagated from the parent function.
  deriving (Data, Functor, Foldable, Traversable)

data LamClause = LamClause { lamLHS      :: LHS
                           , lamRHS      :: RHS
                           , lamWhere    :: WhereClause -- ^ always 'NoWhere' (see parser)
                           , lamCatchAll :: Bool }
  deriving Data

-- | An expression followed by a where clause.
--   Currently only used to give better a better error message in interaction.
data ExprWhere = ExprWhere Expr WhereClause

-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
type ImportDirective = ImportDirective' Name Name
type Using           = Using'           Name Name
type Renaming        = Renaming'        Name Name

-- | An imported name can be a module or a defined name.
type ImportedName = ImportedName' Name Name

-- | The content of the @as@-clause of the import statement.
data AsName' a = AsName
  { asName  :: a
    -- ^ The \"as\" name.
  , asRange :: Range
    -- ^ The range of the \"as\" keyword.  Retained for highlighting purposes.
  }
  deriving (Data, Show, Functor, Foldable, Traversable)

-- | From the parser, we get an expression for the @as@-'Name', which
--   we have to parse into a 'Name'.
type AsName = AsName' (Either Expr Name)

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
  | Generalize Range [TypeSignature] -- ^ Variables to be generalized, can be hidden and/or irrelevant.
  | Field IsInstance Name (Arg Expr) -- ^ Record field, can be hidden and/or irrelevant.
  | FunClause LHS RHS WhereClause Bool
  | DataSig     Range Induction Name [LamBinding] Expr -- ^ lone data signature in mutual block
  | Data        Range Induction Name [LamBinding] Expr [TypeSignatureOrInstanceBlock]
  | DataDef     Range Induction Name [LamBinding] [TypeSignatureOrInstanceBlock]
  | RecordSig   Range Name [LamBinding] Expr -- ^ lone record signature in mutual block
  | RecordDef   Range Name (Maybe (Ranged Induction)) (Maybe HasEta) (Maybe (Name, IsInstance)) [LamBinding] [Declaration]
  | Record      Range Name (Maybe (Ranged Induction)) (Maybe HasEta) (Maybe (Name, IsInstance)) [LamBinding] Expr [Declaration]
    -- ^ The optional name is a name for the record constructor.
  | Infix Fixity [Name]
  | Syntax      Name Notation -- ^ notation declaration for a name
  | PatternSyn  Range Name [Arg Name] Pattern
  | Mutual      Range [Declaration]  -- @Range@ of the whole @mutual@ block.
  | Abstract    Range [Declaration]
  | Private     Range Origin [Declaration]
    -- ^ In "Agda.Syntax.Concrete.Definitions" we generate private blocks
    --   temporarily, which should be treated different that user-declared
    --   private blocks.  Thus the 'Origin'.
  | InstanceB   Range [Declaration]
  | Macro       Range [Declaration]
  | Postulate   Range [TypeSignatureOrInstanceBlock]
  | Primitive   Range [TypeSignature]
  | Open        Range QName ImportDirective
  | Import      Range QName (Maybe AsName) !OpenShortHand ImportDirective
  | ModuleMacro Range  Name ModuleApplication !OpenShortHand ImportDirective
  | Module      Range QName Telescope [Declaration]
  | UnquoteDecl Range [Name] Expr
  | UnquoteDef  Range [Name] Expr
  | Pragma      Pragma
  deriving Data

data ModuleApplication
  = SectionApp Range Telescope Expr
    -- ^ @tel. M args@
  | RecordModuleInstance Range QName
    -- ^ @M {{...}}@
  deriving Data

data OpenShortHand = DoOpen | DontOpen
  deriving (Data, Eq, Show)

-- Pragmas ----------------------------------------------------------------

data Pragma
  = OptionsPragma             Range [String]
  | BuiltinPragma             Range String QName
  | RewritePragma             Range [QName]
  | ForeignPragma             Range String String       -- ^ first string is backend name
  | CompilePragma             Range String QName String -- ^ first string is backend name
  | StaticPragma              Range QName
  | InlinePragma              Range Bool QName  -- ^ INLINE or NOINLINE

  | ImpossiblePragma          Range
    -- ^ Throws an internal error in the scope checker.
  | EtaPragma                 Range QName
    -- ^ For coinductive records, use pragma instead of regular
    --   @eta-equality@ definition (as it is might make Agda loop).
  | WarningOnUsage            Range QName String
    -- ^ Applies to the named function
  | InjectivePragma           Range QName
    -- ^ Mark a definition as injective for the pattern matching unifier.
  | DisplayPragma             Range Pattern Expr
    -- ^ Display lhs as rhs (modifies the printer).

  -- Attached (more or less) pragmas handled in the nicifier (Concrete.Definitions):
  | CatchallPragma            Range
    -- ^ Applies to the following function clause.
  | TerminationCheckPragma    Range (TerminationCheck Name)
    -- ^ Applies to the following function (and all that are mutually recursive with it)
    --   or to the functions in the following mutual block.
  | NoPositivityCheckPragma   Range
    -- ^ Applies to the following data/record type or mutual block.
  | PolarityPragma            Range Name [Occurrence]
  | NoUniverseCheckPragma     Range
    -- ^ Applies to the following data/record type.
  deriving Data

---------------------------------------------------------------------------

-- | Modules: Top-level pragmas plus other top-level declarations.

type Module = ([Pragma], [Declaration])

-- | Computes the top-level module name.
--
-- Precondition: The 'Module' has to be well-formed.
-- This means that there are only allowed declarations before the
-- first module declaration, typically import declarations.
-- See 'spanAllowedBeforeModule'.

topLevelModuleName :: Module -> TopLevelModuleName
topLevelModuleName (_, []) = __IMPOSSIBLE__
topLevelModuleName (_, ds) = case spanAllowedBeforeModule ds of
  (_, Module _ n _ _ : _) -> toTopLevelModuleName n
  _ -> __IMPOSSIBLE__

-- | Splits off allowed (= import) declarations before the first
--   non-allowed declaration.
--   After successful parsing, the first non-allowed declaration
--   should be a module declaration.
spanAllowedBeforeModule :: [Declaration] -> ([Declaration], [Declaration])
spanAllowedBeforeModule = span isAllowedBeforeModule
  where
    isAllowedBeforeModule (Pragma OptionsPragma{}) = True
    isAllowedBeforeModule (Pragma BuiltinPragma{}) = True
    isAllowedBeforeModule (Private _ _ ds) = all isAllowedBeforeModule ds
    isAllowedBeforeModule Import{}       = True
    isAllowedBeforeModule ModuleMacro{}  = True
    isAllowedBeforeModule Open{}         = True
    isAllowedBeforeModule _              = False

{--------------------------------------------------------------------------
    Things we parse but are not part of the Agda file syntax
 --------------------------------------------------------------------------}

-- | Extended content of an interaction hole.
data HoleContent' e
  = HoleContentExpr    e   -- ^ @e@
  | HoleContentRewrite [e] -- ^ @rewrite e0 | ... | en@
  deriving (Functor, Foldable, Traversable)

type HoleContent = HoleContent' Expr

{--------------------------------------------------------------------------
    Views
 --------------------------------------------------------------------------}

-- | The 'Expr' is not an application.
data AppView = AppView Expr [NamedArg Expr]

appView :: Expr -> AppView
appView e =
  case e of
    App r e1 e2     -> vApp (appView e1) e2
    RawApp _ (e:es) -> AppView e $ map arg es
    _               ->  AppView e []
  where
    vApp (AppView e es) arg = AppView e (es ++ [arg])

    arg (HiddenArg   _ e) = hide         $ defaultArg e
    arg (InstanceArg _ e) = makeInstance $ defaultArg e
    arg e                 = defaultArg (unnamed e)

isSingleIdentifierP :: Pattern -> Maybe Name
isSingleIdentifierP p = case removeSingletonRawAppP p of
  IdentP (QName x) -> Just x
  WildP r          -> Just $ noName r
  _                -> Nothing

removeSingletonRawAppP :: Pattern -> Pattern
removeSingletonRawAppP p = case p of
    RawAppP _ [p'] -> removeSingletonRawAppP p'
    ParenP _ p'    -> removeSingletonRawAppP p'
    _ -> p

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

-- Null
------------------------------------------------------------------------

-- | A 'WhereClause' is 'null' when the @where@ keyword is absent.
--   An empty list of declarations does not count as 'null' here.

instance Null (WhereClause' a) where
  empty = NoWhere
  null NoWhere = True
  null AnyWhere{} = False
  null SomeWhere{} = False

-- Lenses
------------------------------------------------------------------------

instance LensHiding LamBinding where
  getHiding   (DomainFree x) = getHiding x
  getHiding   (DomainFull a) = getHiding a
  mapHiding f (DomainFree x) = DomainFree $ mapHiding f x
  mapHiding f (DomainFull a) = DomainFull $ mapHiding f a

instance LensHiding TypedBinding where
  getHiding (TBind _ (x : _) _) = getHiding x   -- Slightly dubious
  getHiding (TBind _ [] _)      = __IMPOSSIBLE__
  getHiding TLet{}              = mempty
  mapHiding f (TBind r xs e) = TBind r ((map . mapHiding) f xs) e
  mapHiding f b@TLet{}       = b

instance LensRelevance TypedBinding where
  getRelevance (TBind _ (x : _) _) = getRelevance x   -- Slightly dubious
  getRelevance (TBind _ [] _)      = __IMPOSSIBLE__
  getRelevance TLet{}              = mempty
  mapRelevance f (TBind r xs e) = TBind r ((map . mapRelevance) f xs) e
  mapRelevance f b@TLet{}       = b

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
      PropN r _          -> r
      Let r _ _          -> r
      Paren r _          -> r
      IdiomBrackets r _  -> r
      DoBlock r _        -> r
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
      Ellipsis r         -> r
      Generalized e      -> getRange e

-- instance HasRange Telescope where
--     getRange (TeleBind bs) = getRange bs
--     getRange (TeleFun x y) = fuseRange x y

instance HasRange TypedBinding where
  getRange (TBind r _ _) = r
  getRange (TLet r _)    = r

instance HasRange LamBinding where
  getRange (DomainFree x) = getRange x
  getRange (DomainFull b) = getRange b

instance HasRange BoundName where
  getRange = getRange . boundName

instance HasRange WhereClause where
  getRange  NoWhere         = noRange
  getRange (AnyWhere ds)    = getRange ds
  getRange (SomeWhere _ _ ds) = getRange ds

instance HasRange ModuleApplication where
  getRange (SectionApp r _ _) = r
  getRange (RecordModuleInstance r _) = r

instance HasRange a => HasRange (FieldAssignment' a) where
  getRange (FieldAssignment a b) = fuseRange a b

instance HasRange ModuleAssignment where
  getRange (ModuleAssignment a b c) = fuseRange a b `fuseRange` c

instance HasRange Declaration where
  getRange (TypeSig _ x t)         = fuseRange x t
  getRange (Field _ x t)           = fuseRange x t
  getRange (FunClause lhs rhs wh _) = fuseRange lhs rhs `fuseRange` wh
  getRange (DataSig r _ _ _ _)     = r
  getRange (Data r _ _ _ _ _)      = r
  getRange (DataDef r _ _ _ _)     = r
  getRange (RecordSig r _ _ _)     = r
  getRange (RecordDef r _ _ _ _ _ _) = r
  getRange (Record r _ _ _ _ _ _ _)  = r
  getRange (Mutual r _)            = r
  getRange (Abstract r _)          = r
  getRange (Generalize r _)        = r
  getRange (Open r _ _)            = r
  getRange (ModuleMacro r _ _ _ _) = r
  getRange (Import r _ _ _ _)      = r
  getRange (InstanceB r _)         = r
  getRange (Macro r _)             = r
  getRange (Private r _ _)         = r
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
  getRange (LHS p eqns ws) = fuseRange p (eqns ++ ws)

instance HasRange LHSCore where
  getRange (LHSHead f ps)              = fuseRange f ps
  getRange (LHSProj d ps1 lhscore ps2) = d `fuseRange` ps1 `fuseRange` lhscore `fuseRange` ps2
  getRange (LHSWith f wps ps)          = f `fuseRange` wps `fuseRange` ps

instance HasRange RHS where
  getRange AbsurdRHS = noRange
  getRange (RHS e)   = getRange e

instance HasRange LamClause where
  getRange (LamClause lhs rhs wh _) = getRange (lhs, rhs, wh)

instance HasRange DoStmt where
  getRange (DoBind r _ _ _) = r
  getRange (DoThen e)       = getRange e
  getRange (DoLet r _)      = r

instance HasRange Pragma where
  getRange (OptionsPragma r _)               = r
  getRange (BuiltinPragma r _ _)             = r
  getRange (RewritePragma r _)               = r
  getRange (CompilePragma r _ _ _)           = r
  getRange (ForeignPragma r _ _)             = r
  getRange (StaticPragma r _)                = r
  getRange (InjectivePragma r _)             = r
  getRange (InlinePragma r _ _)              = r
  getRange (ImpossiblePragma r)              = r
  getRange (EtaPragma r _)                   = r
  getRange (TerminationCheckPragma r _)      = r
  getRange (WarningOnUsage r _ _)            = r
  getRange (CatchallPragma r)                = r
  getRange (DisplayPragma r _ _)             = r
  getRange (NoPositivityCheckPragma r)       = r
  getRange (PolarityPragma r _ _)            = r
  getRange (NoUniverseCheckPragma r)         = r

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
  getRange (EqualP r _)       = r
  getRange (EllipsisP r)      = r
  getRange (WithP r _)        = r

-- SetRange instances
------------------------------------------------------------------------

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
  setRange r (EqualP _ es)      = EqualP r es
  setRange r (EllipsisP _)      = EllipsisP r
  setRange r (WithP _ p)        = WithP r p

instance SetRange TypedBinding where
  setRange r (TBind _ xs e) = TBind r xs e
  setRange r (TLet _ ds)    = TLet r ds

-- KillRange instances
------------------------------------------------------------------------

instance KillRange a => KillRange (FieldAssignment' a) where
  killRange (FieldAssignment a b) = killRange2 FieldAssignment a b

instance KillRange ModuleAssignment where
  killRange (ModuleAssignment a b c) = killRange3 ModuleAssignment a b c

instance KillRange AsName where
  killRange (AsName n _) = killRange1 (flip AsName noRange) n

instance KillRange BoundName where
  killRange (BName n f) = killRange2 BName n f

instance KillRange Declaration where
  killRange (TypeSig i n e)         = killRange2 (TypeSig i) n e
  killRange (Generalize r ds )      = killRange1 (Generalize noRange) ds
  killRange (Field i n a)           = killRange2 (Field i) n a
  killRange (FunClause l r w ca)    = killRange4 FunClause l r w ca
  killRange (DataSig _ i n l e)     = killRange4 (DataSig noRange) i n l e
  killRange (Data _ i n l e c)      = killRange4 (Data noRange i) n l e c
  killRange (DataDef _ i n l c)     = killRange3 (DataDef noRange i) n l c
  killRange (RecordSig _ n l e)     = killRange3 (RecordSig noRange) n l e
  killRange (RecordDef _ n mi mb mn k d) = killRange6 (RecordDef noRange) n mi mb mn k d
  killRange (Record _ n mi mb mn k e d)  = killRange7 (Record noRange) n mi mb mn k e d
  killRange (Infix f n)             = killRange2 Infix f n
  killRange (Syntax n no)           = killRange1 (\n -> Syntax n no) n
  killRange (PatternSyn _ n ns p)   = killRange3 (PatternSyn noRange) n ns p
  killRange (Mutual _ d)            = killRange1 (Mutual noRange) d
  killRange (Abstract _ d)          = killRange1 (Abstract noRange) d
  killRange (Private _ o d)         = killRange2 (Private noRange) o d
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
  killRange (PropN _ n)          = PropN noRange n
  killRange (Rec _ ne)           = killRange1 (Rec noRange) ne
  killRange (RecUpdate _ e ne)   = killRange2 (RecUpdate noRange) e ne
  killRange (Let _ d e)          = killRange2 (Let noRange) d e
  killRange (Paren _ e)          = killRange1 (Paren noRange) e
  killRange (IdiomBrackets _ e)  = killRange1 (IdiomBrackets noRange) e
  killRange (DoBlock _ ss)       = killRange1 (DoBlock noRange) ss
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
  killRange (Ellipsis _)         = Ellipsis noRange
  killRange (Generalized e)      = killRange1 Generalized e

instance KillRange LamBinding where
  killRange (DomainFree b) = killRange1 DomainFree b
  killRange (DomainFull t) = killRange1 DomainFull t

instance KillRange LHS where
  killRange (LHS p r w)     = killRange3 LHS p r w

instance KillRange LamClause where
  killRange (LamClause a b c d) = killRange4 LamClause a b c d

instance KillRange DoStmt where
  killRange (DoBind r p e w) = killRange4 DoBind r p e w
  killRange (DoThen e)       = killRange1 DoThen e
  killRange (DoLet r ds)     = killRange2 DoLet r ds

instance KillRange ModuleApplication where
  killRange (SectionApp _ t e)    = killRange2 (SectionApp noRange) t e
  killRange (RecordModuleInstance _ q) = killRange1 (RecordModuleInstance noRange) q

instance KillRange e => KillRange (OpApp e) where
  killRange (SyntaxBindingLambda _ l e) = killRange2 (SyntaxBindingLambda noRange) l e
  killRange (Ordinary e)                = killRange1 Ordinary e

instance KillRange Pattern where
  killRange (IdentP q)        = killRange1 IdentP q
  killRange (AppP p ps)       = killRange2 AppP p ps
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
  killRange (EqualP _ es)     = killRange1 (EqualP noRange) es
  killRange (EllipsisP _)     = EllipsisP noRange
  killRange (WithP _ p)       = killRange1 (WithP noRange) p

instance KillRange Pragma where
  killRange (OptionsPragma _ s)               = OptionsPragma noRange s
  killRange (BuiltinPragma _ s e)             = killRange1 (BuiltinPragma noRange s) e
  killRange (RewritePragma _ qs)              = killRange1 (RewritePragma noRange) qs
  killRange (StaticPragma _ q)                = killRange1 (StaticPragma noRange) q
  killRange (InjectivePragma _ q)             = killRange1 (InjectivePragma noRange) q
  killRange (InlinePragma _ b q)              = killRange1 (InlinePragma noRange b) q
  killRange (CompilePragma _ b q s)           = killRange1 (\ q -> CompilePragma noRange b q s) q
  killRange (ForeignPragma _ b s)             = ForeignPragma noRange b s
  killRange (ImpossiblePragma _)              = ImpossiblePragma noRange
  killRange (TerminationCheckPragma _ t)      = TerminationCheckPragma noRange (killRange t)
  killRange (WarningOnUsage _ nm str)         = WarningOnUsage noRange (killRange nm) str
  killRange (CatchallPragma _)                = CatchallPragma noRange
  killRange (DisplayPragma _ lhs rhs)         = killRange2 (DisplayPragma noRange) lhs rhs
  killRange (EtaPragma _ q)                   = killRange1 (EtaPragma noRange) q
  killRange (NoPositivityCheckPragma _)       = NoPositivityCheckPragma noRange
  killRange (PolarityPragma _ q occs)         = killRange1 (\q -> PolarityPragma noRange q occs) q
  killRange (NoUniverseCheckPragma _)         = NoUniverseCheckPragma noRange

instance KillRange RHS where
  killRange AbsurdRHS = AbsurdRHS
  killRange (RHS e)   = killRange1 RHS e

instance KillRange TypedBinding where
  killRange (TBind _ b e) = killRange2 (TBind noRange) b e
  killRange (TLet r ds)   = killRange2 TLet r ds

instance KillRange WhereClause where
  killRange NoWhere         = NoWhere
  killRange (AnyWhere d)    = killRange1 AnyWhere d
  killRange (SomeWhere n a d) = killRange3 SomeWhere n a d

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
  rnf (PropN _ a)        = rnf a
  rnf (Rec _ a)          = rnf a
  rnf (RecUpdate _ a b)  = rnf a `seq` rnf b
  rnf (Let _ a b)        = rnf a `seq` rnf b
  rnf (Paren _ a)        = rnf a
  rnf (IdiomBrackets _ a)= rnf a
  rnf (DoBlock _ a)      = rnf a
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
  rnf (Ellipsis _)       = ()
  rnf (Generalized e)    = rnf e

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
  rnf (EqualP _ es) = rnf es
  rnf (EllipsisP _) = ()
  rnf (WithP _ a) = rnf a

-- | Ranges are not forced.

instance NFData Declaration where
  rnf (TypeSig a b c)         = rnf a `seq` rnf b `seq` rnf c
  rnf (Generalize _ a)        = rnf a
  rnf (Field a b c)           = rnf a `seq` rnf b `seq` rnf c
  rnf (FunClause a b c d)     = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (DataSig _ a b c d)     = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (Data _ a b c d e)      = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e
  rnf (DataDef _ a b c d)     = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (RecordSig _ a b c)     = rnf a `seq` rnf b `seq` rnf c
  rnf (RecordDef _ a b c d e f) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e `seq` rnf f
  rnf (Record _ a b c d e f g)  = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e `seq` rnf f `seq` rnf g
  rnf (Infix a b)             = rnf a `seq` rnf b
  rnf (Syntax a b)            = rnf a `seq` rnf b
  rnf (PatternSyn _ a b c)    = rnf a `seq` rnf b `seq` rnf c
  rnf (Mutual _ a)            = rnf a
  rnf (Abstract _ a)          = rnf a
  rnf (Private _ _ a)         = rnf a
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
  rnf (CompilePragma _ a b c)           = rnf a `seq` rnf b `seq` rnf c
  rnf (ForeignPragma _ b s)             = rnf b `seq` rnf s
  rnf (StaticPragma _ a)                = rnf a
  rnf (InjectivePragma _ a)             = rnf a
  rnf (InlinePragma _ _ a)              = rnf a
  rnf (ImpossiblePragma _)              = ()
  rnf (EtaPragma _ a)                   = rnf a
  rnf (TerminationCheckPragma _ a)      = rnf a
  rnf (WarningOnUsage _ a b)            = rnf a `seq` rnf b
  rnf (CatchallPragma _)                = ()
  rnf (DisplayPragma _ a b)             = rnf a `seq` rnf b
  rnf (NoPositivityCheckPragma _)       = ()
  rnf (PolarityPragma _ a b)            = rnf a `seq` rnf b
  rnf (NoUniverseCheckPragma _)         = ()

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
  rnf (RecordModuleInstance _ a) = rnf a

-- | Ranges are not forced.

instance NFData a => NFData (OpApp a) where
  rnf (SyntaxBindingLambda _ a b) = rnf a `seq` rnf b
  rnf (Ordinary a)                = rnf a

-- | Ranges are not forced.

instance NFData LHS where
  rnf (LHS a b c) = rnf a `seq` rnf b `seq` rnf c

instance NFData a => NFData (FieldAssignment' a) where
  rnf (FieldAssignment a b) = rnf a `seq` rnf b

instance NFData ModuleAssignment where
  rnf (ModuleAssignment a b c) = rnf a `seq` rnf b `seq` rnf c

instance NFData a => NFData (WhereClause' a) where
  rnf NoWhere         = ()
  rnf (AnyWhere a)    = rnf a
  rnf (SomeWhere a b c) = rnf a `seq` rnf b `seq` rnf c

instance NFData LamClause where
  rnf (LamClause a b c d) = rnf (a, b, c, d)

instance NFData a => NFData (LamBinding' a) where
  rnf (DomainFree a) = rnf a
  rnf (DomainFull a) = rnf a

instance NFData BoundName where
  rnf (BName a b) = rnf a `seq` rnf b

instance NFData a => NFData (RHS' a) where
  rnf AbsurdRHS = ()
  rnf (RHS a)   = rnf a

instance NFData DoStmt where
  rnf (DoBind _ p e w) = rnf (p, e, w)
  rnf (DoThen e)       = rnf e
  rnf (DoLet _ ds)     = rnf ds
