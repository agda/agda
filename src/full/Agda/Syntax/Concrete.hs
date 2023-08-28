{-# LANGUAGE CPP #-}
{-# LANGUAGE ApplicativeDo #-}  -- see exprToPattern

{-| The concrete syntax is a raw representation of the program text
    without any desugaring at all.  This is what the parser produces.
    The idea is that if we figure out how to keep the concrete syntax
    around, it can be printed exactly as the user wrote it.
-}
module Agda.Syntax.Concrete
  ( -- * Expressions
    Expr(..)
  , OpApp(..), fromOrdinary
  , OpAppArgs, OpAppArgs'
  , module Agda.Syntax.Concrete.Name
  , AppView(..), appView, unAppView
  , rawApp, rawAppP
  , isSingleIdentifierP, removeParenP
  , isPattern, isAbsurdP, isBinderP
  , observeHiding
  , observeRelevance
  , observeModifiers
  , exprToPatternWithHoles
  , returnExpr
    -- * Bindings
  , Binder'(..)
  , Binder
  , mkBinder_
  , mkBinder
  , LamBinding
  , LamBinding'(..)
  , dropTypeAndModality
  , TypedBinding
  , TypedBinding'(..)
  , RecordAssignment
  , RecordAssignments
  , FieldAssignment, FieldAssignment'(..), nameFieldA, exprFieldA
  , ModuleAssignment(..)
  , BoundName(..), mkBoundName_, mkBoundName
  , TacticAttribute
  , Telescope, Telescope1
  , lamBindingsToTelescope
  , makePi
  , mkLam, mkLet, mkTLet
    -- * Declarations
  , Declaration(..)
  , isPragma
  , isRecordDirective
  , RecordDirective(..)
  , RecordDirectives
  , ModuleApplication(..)
  , TypeSignature
  , TypeSignatureOrInstanceBlock
  , ImportDirective, Using, ImportedName
  , Renaming, RenamingDirective, HidingDirective
  , AsName'(..), AsName
  , OpenShortHand(..), RewriteEqn, WithExpr
  , LHS(..), Pattern(..), LHSCore(..)
  , LamClause(..)
  , RHS, RHS'(..), WhereClause, WhereClause'(..), ExprWhere(..)
  , DoStmt(..)
  , Pragma(..)
  , Module(..)
  , ThingWithFixity(..)
  , HoleContent, HoleContent'(..)
  , spanAllowedBeforeModule
  )
  where

import Prelude hiding (null)

import Control.DeepSeq

import qualified Data.DList as DL
import Data.Functor.Identity
import Data.Set         ( Set  )
import Data.Text        ( Text )
-- import Data.Traversable ( forM )

import GHC.Generics     ( Generic )

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Literal

import Agda.Syntax.Concrete.Name
import qualified Agda.Syntax.Abstract.Name as A

import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.Applicative ( forA )
import Agda.Utils.Either      ( maybeLeft )
import Agda.Utils.Lens
import Agda.Utils.List1       ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.List2       ( List2, pattern List2 )
import Agda.Syntax.Common.Aspect (NameKind)
import Agda.Utils.Null
import Agda.Utils.Singleton

import Agda.Utils.Impossible

data OpApp e
  = SyntaxBindingLambda Range (List1 LamBinding) e
    -- ^ An abstraction inside a special syntax declaration
    --   (see Issue 358 why we introduce this).
  | Ordinary e
  deriving (Functor, Foldable, Traversable, Eq)

fromOrdinary :: e -> OpApp e -> e
fromOrdinary d (Ordinary e) = e
fromOrdinary d _            = d

data FieldAssignment' a = FieldAssignment { _nameFieldA :: Name, _exprFieldA :: a }
  deriving (Functor, Foldable, Traversable, Show, Eq)

type FieldAssignment = FieldAssignment' Expr

data ModuleAssignment  = ModuleAssignment
                           { _qnameModA     :: QName
                           , _exprModA      :: [Expr]
                           , _importDirModA :: ImportDirective
                           }
  deriving Eq

type RecordAssignment  = Either FieldAssignment ModuleAssignment
type RecordAssignments = [RecordAssignment]

nameFieldA :: Lens' (FieldAssignment' a) Name
nameFieldA f r = f (_nameFieldA r) <&> \x -> r { _nameFieldA = x }

exprFieldA :: Lens' (FieldAssignment' a) a
exprFieldA f r = f (_exprFieldA r) <&> \x -> r { _exprFieldA = x }

-- UNUSED Liang-Ting Chen 2019-07-16
--qnameModA :: Lens' ModuleAssignment QName
--qnameModA f r = f (_qnameModA r) <&> \x -> r { _qnameModA = x }
--
--exprModA :: Lens' [Expr] ModuleAssignment
--exprModA f r = f (_exprModA r) <&> \x -> r { _exprModA = x }
--
--importDirModA :: Lens' ModuleAssignment ImportDirective
--importDirModA f r = f (_importDirModA r) <&> \x -> r { _importDirModA = x }

-- | Concrete expressions. Should represent exactly what the user wrote.
data Expr
  = Ident QName                                -- ^ ex: @x@
  | Lit Range Literal                          -- ^ ex: @1@ or @\"foo\"@
  | QuestionMark Range (Maybe Nat)             -- ^ ex: @?@ or @{! ... !}@
  | Underscore Range (Maybe String)            -- ^ ex: @_@ or @_A_5@
  | RawApp Range (List2 Expr)                  -- ^ before parsing operators
  | App Range Expr (NamedArg Expr)             -- ^ ex: @e e@, @e {e}@, or @e {x = e}@
  | OpApp Range QName (Set A.Name) OpAppArgs   -- ^ ex: @e + e@
                                               -- The 'QName' is possibly ambiguous,
                                               -- but it must correspond to one of the names in the set.
  | WithApp Range Expr [Expr]                  -- ^ ex: @e | e1 | .. | en@
  | HiddenArg Range (Named_ Expr)              -- ^ ex: @{e}@ or @{x=e}@
  | InstanceArg Range (Named_ Expr)            -- ^ ex: @{{e}}@ or @{{x=e}}@
  | Lam Range (List1 LamBinding) Expr          -- ^ ex: @\\x {y} -> e@ or @\\(x:A){y:B} -> e@
  | AbsurdLam Range Hiding                     -- ^ ex: @\\ ()@
  | ExtendedLam Range Erased
      (List1 LamClause)                        -- ^ ex: @\\ { p11 .. p1a -> e1 ; .. ; pn1 .. pnz -> en }@
  | Fun Range (Arg Expr) Expr                  -- ^ ex: @e -> e@ or @.e -> e@ (NYI: @{e} -> e@)
  | Pi Telescope1 Expr                         -- ^ ex: @(xs:e) -> e@ or @{xs:e} -> e@
  | Rec Range RecordAssignments                -- ^ ex: @record {x = a; y = b}@, or @record { x = a; M1; M2 }@
  | RecUpdate Range Expr [FieldAssignment]     -- ^ ex: @record e {x = a; y = b}@
  | Let Range (List1 Declaration) (Maybe Expr) -- ^ ex: @let Ds in e@, missing body when parsing do-notation let
  | Paren Range Expr                           -- ^ ex: @(e)@
  | IdiomBrackets Range [Expr]                 -- ^ ex: @(| e1 | e2 | .. | en |)@ or @(|)@
  | DoBlock Range (List1 DoStmt)               -- ^ ex: @do x <- m1; m2@
  | Absurd Range                               -- ^ ex: @()@ or @{}@, only in patterns
  | As Range Name Expr                         -- ^ ex: @x\@p@, only in patterns
  | Dot Range Expr                             -- ^ ex: @.p@, only in patterns
  | DoubleDot Range Expr                       -- ^ ex: @..A@, used for parsing @..A -> B@
  | Quote Range                                -- ^ ex: @quote@, should be applied to a name
  | QuoteTerm Range                            -- ^ ex: @quoteTerm@, should be applied to a term
  | Tactic Range Expr                          -- ^ ex: @\@(tactic t)@, used to declare tactic arguments
  | Unquote Range                              -- ^ ex: @unquote@, should be applied to a term of type @Term@
  | DontCare Expr                              -- ^ to print irrelevant things
  | Equal Range Expr Expr                      -- ^ ex: @a = b@, used internally in the parser
  | Ellipsis Range                             -- ^ @...@, used internally to parse patterns.
  | KnownIdent NameKind QName
    -- ^ An identifier coming from abstract syntax, for which we know a
    -- precise syntactic highlighting class (used in printing).
  | KnownOpApp NameKind Range QName (Set A.Name) OpAppArgs
    -- ^ An operator application coming from abstract syntax, for which
    -- we know a precise syntactic highlighting class (used in
    -- printing).
  | Generalized Expr
  deriving Eq

type OpAppArgs = OpAppArgs' Expr
type OpAppArgs' e = [NamedArg (MaybePlaceholder (OpApp e))]

-- | Concrete patterns. No literals in patterns at the moment.
data Pattern
  = IdentP Bool QName                      -- ^ @c@ or @x@
                                           --
                                           -- If the boolean is
                                           -- 'False', then the
                                           -- 'QName' must not refer
                                           -- to a constructor or a
                                           -- pattern synonym. The
                                           -- value 'False' is used
                                           -- when a hidden argument
                                           -- pun is expanded.
  | QuoteP Range                           -- ^ @quote@
  | AppP Pattern (NamedArg Pattern)        -- ^ @p p'@ or @p {x = p'}@
  | RawAppP Range (List2 Pattern)          -- ^ @p1..pn@ before parsing operators
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
  | LitP Range Literal                     -- ^ @0@, @1@, etc.
  | RecP Range [FieldAssignment' Pattern]  -- ^ @record {x = p; y = q}@
  | EqualP Range [(Expr,Expr)]             -- ^ @i = i1@ i.e. cubical face lattice generator
  | EllipsisP Range (Maybe Pattern)        -- ^ @...@, only as left-most pattern.
                                           --   Second arg is @Nothing@ before expansion, and
                                           --   @Just p@ after expanding ellipsis to @p@.
  | WithP Range Pattern                    -- ^ @| p@, for with-patterns.
  deriving Eq

data DoStmt
  = DoBind Range Pattern Expr [LamClause]   -- ^ @p ← e where cs@
  | DoThen Expr
  | DoLet Range (List1 Declaration)
  deriving Eq

-- | A Binder @x\@p@, the pattern is optional
data Binder' a = Binder
  { binderPattern :: Maybe Pattern
  , binderName    :: a
  } deriving (Eq, Functor, Foldable, Traversable)

type Binder = Binder' BoundName

mkBinder_ :: Name -> Binder
mkBinder_ = mkBinder . mkBoundName_

mkBinder :: a -> Binder' a
mkBinder = Binder Nothing

-- | A lambda binding is either domain free or typed.

type LamBinding = LamBinding' TypedBinding
data LamBinding' a
  = DomainFree (NamedArg Binder)
    -- ^ . @x@ or @{x}@ or @.x@ or @.{x}@ or @{.x}@ or @x\@p@ or @(p)@
  | DomainFull a
    -- ^ . @(xs : e)@ or @{xs : e}@
  deriving (Functor, Foldable, Traversable, Eq)

-- | Drop type annotations and lets from bindings.
dropTypeAndModality :: LamBinding -> [LamBinding]
dropTypeAndModality (DomainFull (TBind _ xs _)) =
  map (DomainFree . setModality defaultModality) $ List1.toList xs
dropTypeAndModality (DomainFull TLet{}) = []
dropTypeAndModality (DomainFree x) = [DomainFree $ setModality defaultModality x]

data BoundName = BName
  { boundName       :: Name
  , bnameFixity     :: Fixity'
  , bnameTactic     :: TacticAttribute -- From @tactic attribute
  , bnameIsFinite   :: Bool
  }
  deriving Eq

type TacticAttribute = Maybe (Ranged Expr)

mkBoundName_ :: Name -> BoundName
mkBoundName_ x = mkBoundName x noFixity'

mkBoundName :: Name -> Fixity' -> BoundName
mkBoundName x f = BName x f Nothing False

-- | A typed binding.

type TypedBinding = TypedBinding' Expr

data TypedBinding' e
  = TBind Range (List1 (NamedArg Binder)) e
    -- ^ Binding @(x1\@p1 ... xn\@pn : A)@.
  | TLet  Range (List1 Declaration)
    -- ^ Let binding @(let Ds)@ or @(open M args)@.
  deriving (Functor, Foldable, Traversable, Eq)

-- | A telescope is a sequence of typed bindings. Bound variables are in scope
--   in later types.
type Telescope1 = List1 TypedBinding
type Telescope  = [TypedBinding]

-- | We can try to get a @Telescope@ from a @[LamBinding]@.
--   If we have a type annotation already, we're happy.
--   Otherwise we manufacture a binder with an underscore for the type.
lamBindingsToTelescope :: Range -> [LamBinding] -> Telescope
lamBindingsToTelescope r = fmap $ \case
  DomainFull ty -> ty
  DomainFree nm -> TBind r (List1.singleton nm) $ Underscore r Nothing

-- | Smart constructor for @Pi@: check whether the @Telescope@ is empty

makePi :: Telescope -> Expr -> Expr
makePi []     = id
makePi (b:bs) = Pi (b :| bs)

-- | Smart constructor for @Lam@: check for non-zero bindings.

mkLam :: Range -> [LamBinding] -> Expr -> Expr
mkLam r []     e = e
mkLam r (x:xs) e = Lam r (x :| xs) e

-- | Smart constructor for @Let@: check for non-zero let bindings.

mkLet :: Range -> [Declaration] -> Expr -> Expr
mkLet r []     e = e
mkLet r (d:ds) e = Let r (d :| ds) (Just e)

-- | Smart constructor for @TLet@: check for non-zero let bindings.

mkTLet :: Range -> [Declaration] -> Maybe (TypedBinding' e)
mkTLet r []     = Nothing
mkTLet r (d:ds) = Just $ TLet r (d :| ds)

{-| Left hand sides can be written in infix style. For example:

    > n + suc m = suc (n + m)
    > (f ∘ g) x = f (g x)

   We use fixity information to see which name is actually defined.
-}
data LHS = LHS  -- ^ Original pattern (including with-patterns), rewrite equations and with-expressions.
  { lhsOriginalPattern :: Pattern
    -- ^ e.g. @f ps | wps@
  , lhsRewriteEqn      :: [RewriteEqn]
    -- ^ @(rewrite e | with p <- e in eq)@ (many)
  , lhsWithExpr        :: [WithExpr]
    -- ^ @with e1 in eq | {e2} | ...@ (many)
  }
  deriving Eq

type RewriteEqn = RewriteEqn' () Name Pattern Expr
type WithExpr   = Named Name (Arg Expr)

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
  | LHSEllipsis
             { lhsEllipsisRange :: Range
             , lhsEllipsisPat   :: LHSCore           -- ^ Pattern that was expanded from an ellipsis @...@.
             }
  deriving Eq

type RHS = RHS' Expr
data RHS' e
  = AbsurdRHS -- ^ No right hand side because of absurd match.
  | RHS e
  deriving (Functor, Foldable, Traversable, Eq)

-- | @where@ block following a clause.
type WhereClause = WhereClause' [Declaration]

-- The generalization @WhereClause'@ is for the sake of Concrete.Generic.
data WhereClause' decls
  = NoWhere
      -- ^ No @where@ clauses.
  | AnyWhere Range decls
      -- ^ Ordinary @where@.  'Range' of the @where@ keyword.
      --   List of declarations can be empty.
  | SomeWhere Range Erased Name Access decls
      -- ^ Named where: @module M where ds@.
      --   'Range' of the keywords @module@ and @where@.
      --   The 'Access' flag applies to the 'Name' (not the module contents!)
      --   and is propagated from the parent function.
      --   List of declarations can be empty.
  deriving (Eq, Functor, Foldable, Traversable)

data LamClause = LamClause
  { lamLHS      :: [Pattern]   -- ^ Possibly empty sequence.
  , lamRHS      :: RHS
  , lamCatchAll :: Bool
  }
  deriving Eq

-- | An expression followed by a where clause.
--   Currently only used to give better a better error message in interaction.
data ExprWhere = ExprWhere Expr WhereClause

-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
type ImportDirective = ImportDirective' Name Name
type Using           = Using'           Name Name
type Renaming        = Renaming'        Name Name
type RenamingDirective = RenamingDirective' Name Name
type HidingDirective   = HidingDirective'   Name Name  -- 'Hiding' is already taken

-- | An imported name can be a module or a defined name.
type ImportedName = ImportedName' Name Name

-- | The content of the @as@-clause of the import statement.
data AsName' a = AsName
  { asName  :: a
    -- ^ The \"as\" name.
  , asRange :: Range
    -- ^ The range of the \"as\" keyword.  Retained for highlighting purposes.
  }
  deriving (Show, Functor, Foldable, Traversable, Eq)

-- | From the parser, we get an expression for the @as@-'Name', which
--   we have to parse into a 'Name'.
type AsName = AsName' (Either Expr Name)

{--------------------------------------------------------------------------
    Declarations
 --------------------------------------------------------------------------}

-- | Just type signatures.
type TypeSignature = Declaration

-- | Just field signatures
type FieldSignature = Declaration

-- | Just type signatures or instance blocks.
type TypeSignatureOrInstanceBlock = Declaration

-- | Isolated record directives parsed as Declarations
data RecordDirective
   = Induction (Ranged Induction)
       -- ^ Range of keyword @[co]inductive@.
   | Constructor Name IsInstance
   | Eta         (Ranged HasEta0)
       -- ^ Range of @[no-]eta-equality@ keyword.
   | PatternOrCopattern Range
       -- ^ If declaration @pattern@ is present, give its range.
   deriving (Eq, Show)

type RecordDirectives = RecordDirectives' (Name, IsInstance)

{-| The representation type of a declaration. The comments indicate
    which type in the intended family the constructor targets.
-}

data Declaration
  = TypeSig ArgInfo TacticAttribute Name Expr
      -- ^ Axioms and functions can be irrelevant. (Hiding should be NotHidden)
  | FieldSig IsInstance TacticAttribute Name (Arg Expr)
  | Generalize Range [TypeSignature] -- ^ Variables to be generalized, can be hidden and/or irrelevant.
  | Field Range [FieldSignature]
  | FunClause LHS RHS WhereClause Bool
  | DataSig     Range Erased Name [LamBinding] Expr -- ^ lone data signature in mutual block
  | Data        Range Erased Name [LamBinding] Expr
                [TypeSignatureOrInstanceBlock]
  | DataDef     Range Name [LamBinding] [TypeSignatureOrInstanceBlock]
  | RecordSig   Range Erased Name [LamBinding] Expr -- ^ lone record signature in mutual block
  | RecordDef   Range Name RecordDirectives [LamBinding] [Declaration]
  | Record      Range Erased Name RecordDirectives [LamBinding] Expr
                [Declaration]
  | RecordDirective RecordDirective -- ^ Should not survive beyond the parser
  | Infix Fixity (List1 Name)
  | Syntax      Name Notation -- ^ notation declaration for a name
  | PatternSyn  Range Name [Arg Name] Pattern
  | Mutual      Range [Declaration]  -- @Range@ of the whole @mutual@ block.
  | InterleavedMutual Range [Declaration]
  | Abstract    Range [Declaration]
  | Private     Range Origin [Declaration]
    -- ^ In "Agda.Syntax.Concrete.Definitions" we generate private blocks
    --   temporarily, which should be treated different that user-declared
    --   private blocks.  Thus the 'Origin'.
  | InstanceB   Range [Declaration]
    -- ^ The 'Range' here (exceptionally) only refers to the range of the
    --   @instance@ keyword.  The range of the whole block @InstanceB r ds@
    --   is @fuseRange r ds@.
  | LoneConstructor Range [Declaration]
  | Macro       Range [Declaration]
  | Postulate   Range [TypeSignatureOrInstanceBlock]
  | Primitive   Range [TypeSignature]
  | Open        Range QName ImportDirective
  | Import      Range QName (Maybe AsName) !OpenShortHand ImportDirective
  | ModuleMacro Range Erased  Name ModuleApplication !OpenShortHand
                ImportDirective
  | Module      Range Erased QName Telescope [Declaration]
  | UnquoteDecl Range [Name] Expr
      -- ^ @unquoteDecl xs = e@
  | UnquoteDef  Range [Name] Expr
      -- ^ @unquoteDef xs = e@
  | UnquoteData Range Name [Name] Expr
      -- ^ @unquoteDecl data d constructor xs = e@
  | Pragma      Pragma
  | Opaque      Range [Declaration]
    -- ^ @opaque ...@
  | Unfolding   Range [QName]
    -- ^ @unfolding ...@
  deriving Eq

-- | Extract a record directive
isRecordDirective :: Declaration -> Maybe RecordDirective
isRecordDirective (RecordDirective r) = Just r
isRecordDirective (InstanceB r [RecordDirective (Constructor n p)]) = Just (Constructor n (InstanceDef r))
isRecordDirective _ = Nothing

-- | Return 'Pragma' if 'Declaration' is 'Pragma'.
{-# SPECIALIZE isPragma :: Declaration -> Maybe Pragma #-}
{-# SPECIALIZE isPragma :: Declaration -> [Pragma] #-}
isPragma :: CMaybe Pragma m => Declaration -> m
isPragma = \case
    Pragma p                -> singleton p
    Private  _ _ _          -> empty
    Abstract _ _            -> empty
    InstanceB _ _           -> empty
    Mutual _ _              -> empty
    Module _ _ _ _ _        -> empty
    Macro _ _               -> empty
    Record _ _ _ _ _ _ _    -> empty
    RecordDef _ _ _ _ _     -> empty
    TypeSig _ _ _ _         -> empty
    FieldSig _ _ _ _        -> empty
    Generalize _ _          -> empty
    Field _ _               -> empty
    FunClause _ _ _ _       -> empty
    DataSig _ _ _ _ _       -> empty
    Data _ _ _ _ _ _        -> empty
    DataDef _ _ _ _         -> empty
    RecordSig _ _ _ _ _     -> empty
    RecordDirective _       -> empty
    Infix _ _               -> empty
    Syntax _ _              -> empty
    PatternSyn _ _ _ _      -> empty
    InterleavedMutual _ _   -> empty
    LoneConstructor _ _     -> empty
    Postulate _ _           -> empty
    Primitive _ _           -> empty
    Open _ _ _              -> empty
    Import _ _ _ _ _        -> empty
    ModuleMacro _ _ _ _ _ _ -> empty
    UnquoteDecl _ _ _       -> empty
    UnquoteDef _ _ _        -> empty
    UnquoteData _ _ _ _     -> empty
    Opaque _ _              -> empty
    Unfolding _ _           -> empty

data ModuleApplication
  = SectionApp Range Telescope Expr
    -- ^ @tel. M args@
  | RecordModuleInstance Range QName
    -- ^ @M {{...}}@
  deriving Eq

data OpenShortHand = DoOpen | DontOpen
  deriving (Eq, Show, Generic)

-- Pragmas ----------------------------------------------------------------

data Pragma
  = OptionsPragma             Range [String]
  | BuiltinPragma             Range RString QName
  | RewritePragma             Range Range [QName]        -- ^ Second Range is for REWRITE keyword.
  | ForeignPragma             Range RString String       -- ^ first string is backend name
  | CompilePragma             Range RString QName String -- ^ first string is backend name
  | StaticPragma              Range QName
  | InlinePragma              Range Bool QName  -- ^ INLINE or NOINLINE

  | ImpossiblePragma          Range [String]
    -- ^ Throws an internal error in the scope checker.
    --   The 'String's are words to be displayed with the error.
  | EtaPragma                 Range QName
    -- ^ For coinductive records, use pragma instead of regular
    --   @eta-equality@ definition (as it is might make Agda loop).
  | WarningOnUsage            Range QName Text
    -- ^ Applies to the named function
  | WarningOnImport           Range Text
    -- ^ Applies to the current module
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
  | NoCoverageCheckPragma     Range
    -- ^ Applies to the following function (and all that are mutually recursive with it)
    --   or to the functions in the following mutual block.
  | NoPositivityCheckPragma   Range
    -- ^ Applies to the following data/record type or mutual block.
  | PolarityPragma            Range Name [Occurrence]
  | NoUniverseCheckPragma     Range
    -- ^ Applies to the following data/record type.
  | NotProjectionLikePragma   Range QName
    -- ^ Applies to the stated function
  deriving Eq

---------------------------------------------------------------------------

-- | Modules: Top-level pragmas plus other top-level declarations.

data Module = Mod
  { modPragmas :: [Pragma]
  , modDecls   :: [Declaration]
  }

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
data HoleContent' qn nm p e
  = HoleContentExpr    e                       -- ^ @e@
  | HoleContentRewrite [RewriteEqn' qn nm p e] -- ^ @(rewrite | invert) e0 | ... | en@
  deriving (Functor, Foldable, Traversable)

type HoleContent = HoleContent' () Name Pattern Expr

---------------------------------------------------------------------------
-- * Smart constructors
---------------------------------------------------------------------------

rawApp :: List1 Expr -> Expr
rawApp es@(e1 :| e2 : rest) = RawApp (getRange es) $ List2 e1 e2 rest
rawApp (e :| []) = e

rawAppP :: List1 Pattern -> Pattern
rawAppP ps@(p1 :| p2 : rest) = RawAppP (getRange ps) $ List2 p1 p2 rest
rawAppP (p :| []) = p

{--------------------------------------------------------------------------
    Views
 --------------------------------------------------------------------------}

-- | The 'Expr' is not an application.
data AppView = AppView Expr [NamedArg Expr]

appView :: Expr -> AppView
appView e = f (DL.toList ess)
  where
    (f, ess) = appView' e

    appView' = \case
      App r e1 e2      -> vApp (appView' e1) e2
      RawApp _ (List2 e1 e2 es)
                       -> (AppView e1, DL.fromList (map arg (e2 : es)))
      e                -> (AppView e, mempty)

    vApp (f, es) arg = (f, es `DL.snoc` arg)

    arg (HiddenArg   _ e) = hide         $ defaultArg e
    arg (InstanceArg _ e) = makeInstance $ defaultArg e
    arg e                 = defaultArg (unnamed e)

unAppView :: AppView -> Expr
unAppView (AppView e nargs) = rawApp (e :| map unNamedArg nargs)

  where
    unNamedArg narg = ($ unArg narg) $ case getHiding narg of
      Hidden     -> HiddenArg (getRange narg)
      NotHidden  -> namedThing
      Instance{} -> InstanceArg (getRange narg)

isSingleIdentifierP :: Pattern -> Maybe Name
isSingleIdentifierP = \case
  IdentP _ (QName x) -> Just x
  WildP r            -> Just $ noName r
  ParenP _ p         -> isSingleIdentifierP p
  _                  -> Nothing

removeParenP :: Pattern -> Pattern
removeParenP = \case
    ParenP _ p -> removeParenP p
    p -> p

-- | Observe the hiding status of an expression
observeHiding :: Expr -> WithHiding Expr
observeHiding = \case
  HiddenArg _   (Named Nothing e) -> WithHiding Hidden e
  InstanceArg _ (Named Nothing e) -> WithHiding (Instance NoOverlap) e
  e                               -> WithHiding NotHidden e

-- | Observe the relevance status of an expression
observeRelevance :: Expr -> (Relevance, Expr)
observeRelevance = \case
  Dot _ e       -> (Irrelevant, e)
  DoubleDot _ e -> (NonStrict, e)
  e             -> (Relevant, e)

-- | Observe various modifiers applied to an expression
observeModifiers :: Expr -> Arg Expr
observeModifiers e =
  let (rel, WithHiding hid e') = fmap observeHiding (observeRelevance e) in
  setRelevance rel $ setHiding hid $ defaultArg e'

returnExpr :: Expr -> Maybe Expr
returnExpr (Pi _ e)        = returnExpr e
returnExpr (Fun _ _  e)    = returnExpr e
returnExpr (Let _ _ e)     = returnExpr =<< e
returnExpr (Paren _ e)     = returnExpr e
returnExpr (Generalized e) = returnExpr e
returnExpr e               = pure e

-- | Turn an expression into a pattern. Fails if the expression is not a
--   valid pattern.

isPattern :: Expr -> Maybe Pattern
isPattern = exprToPattern (const Nothing)

-- | Turn an expression into a pattern, turning non-pattern subexpressions into 'WildP'.

exprToPatternWithHoles :: Expr -> Pattern
exprToPatternWithHoles = runIdentity . exprToPattern (Identity . WildP . getRange)

-- | Generic expression to pattern conversion.

exprToPattern :: Applicative m
  => (Expr -> m Pattern)  -- ^ Default result for non-pattern things.
  -> Expr                 -- ^ The expression to translate.
  -> m Pattern            -- ^ The translated pattern (maybe).
exprToPattern fallback = loop
  where
  loop = \case
    Ident       x        -> pure $ IdentP True x
    App         _ e1 e2  -> AppP <$> loop e1 <*> traverse (traverse loop) e2
    Paren       r e      -> ParenP r <$> loop e
    Underscore  r _      -> pure $ WildP r
    Absurd      r        -> pure $ AbsurdP r
    As          r x e    -> pushUnderBracesP r (AsP r x) <$> loop e
    Dot         r e      -> pure $ pushUnderBracesE r (DotP r) e
    -- Wen, 2020-08-27: We disallow Float patterns, since equality for floating
    -- point numbers is not stable across architectures and with different
    -- compiler flags.
    e@(Lit _ LitFloat{}) -> fallback e
    Lit         r l      -> pure $ LitP r l
    HiddenArg   r e      -> HiddenP   r <$> traverse loop e
    InstanceArg r e      -> InstanceP r <$> traverse loop e
    RawApp      r es     -> RawAppP   r <$> traverse loop es
    Quote       r        -> pure $ QuoteP r
    Equal       r e1 e2  -> pure $ EqualP r [(e1, e2)]
    Ellipsis    r        -> pure $ EllipsisP r Nothing
    e@(Rec r es)
        -- We cannot translate record expressions with module parts.
      | Just fs <- mapM maybeLeft es -> RecP r <$> traverse (traverse loop) fs
      | otherwise -> fallback e
    -- WithApp has already lost the range information of the bars '|'
    WithApp     r e es   -> do -- ApplicativeDo
      p  <- loop e
      ps <- forA es $ \ e -> do -- ApplicativeDo
        p <- loop e
        pure $ defaultNamedArg $ WithP (getRange e) p   -- TODO #2822: Range!
      pure $ foldl AppP p ps
    e -> fallback e

  pushUnderBracesP :: Range -> (Pattern -> Pattern) -> (Pattern -> Pattern)
  pushUnderBracesP r f = \case
    HiddenP   _ p   -> HiddenP   r $ fmap f p
    InstanceP _ p   -> InstanceP r $ fmap f p
    p               -> f p

  pushUnderBracesE :: Range -> (Expr -> Pattern) -> (Expr -> Pattern)
  pushUnderBracesE r f = \case
    HiddenArg   _ p -> HiddenP   r $ fmap f p
    InstanceArg _ p -> InstanceP r $ fmap f p
    p               -> f p

isAbsurdP :: Pattern -> Maybe (Range, Hiding)
isAbsurdP = \case
  AbsurdP r      -> pure (r, NotHidden)
  AsP _ _      p -> isAbsurdP p
  ParenP _     p -> isAbsurdP p
  HiddenP   _ np -> (Hidden <$)              <$> isAbsurdP (namedThing np)
  InstanceP _ np -> (Instance YesOverlap <$) <$> isAbsurdP (namedThing np)
  _ -> Nothing

isBinderP :: Pattern -> Maybe Binder
isBinderP = \case
  IdentP _ qn
             -> mkBinder_ <$> isUnqualified qn
  WildP r    -> pure $ mkBinder_ $ setRange r simpleHole
  AsP r n p  -> pure $ Binder (Just p) $ mkBoundName_ n
  ParenP r p -> pure $ Binder (Just p) $ mkBoundName_ $ setRange r simpleHole
  _ -> Nothing

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
  getHiding (TBind _ (x :| _) _) = getHiding x   -- Slightly dubious
  getHiding TLet{}              = mempty
  mapHiding f (TBind r xs e) = TBind r (fmap (mapHiding f) xs) e
  mapHiding f b@TLet{}       = b

instance LensRelevance TypedBinding where
  getRelevance (TBind _ (x :|_) _) = getRelevance x   -- Slightly dubious
  getRelevance TLet{}              = unitRelevance
  mapRelevance f (TBind r xs e) = TBind r (fmap (mapRelevance f) xs) e
  mapRelevance f b@TLet{}       = b

-- HasRange instances
------------------------------------------------------------------------

instance HasRange e => HasRange (OpApp e) where
  getRange = \case
    Ordinary e -> getRange e
    SyntaxBindingLambda r _ _ -> r

instance HasRange Expr where
  getRange = \case
      Ident x            -> getRange x
      Lit r _            -> r
      QuestionMark r _   -> r
      Underscore r _     -> r
      App r _ _          -> r
      RawApp r _         -> r
      OpApp r _ _ _      -> r
      WithApp r _ _      -> r
      Lam r _ _          -> r
      AbsurdLam r _      -> r
      ExtendedLam r _ _  -> r
      Fun r _ _          -> r
      Pi b e             -> fuseRange b e
      Let r _ _          -> r
      Paren r _          -> r
      IdiomBrackets r _  -> r
      DoBlock r _        -> r
      As r _ _           -> r
      Dot r _            -> r
      DoubleDot r _      -> r
      Absurd r           -> r
      HiddenArg r _      -> r
      InstanceArg r _    -> r
      Rec r _            -> r
      RecUpdate r _ _    -> r
      Quote r            -> r
      QuoteTerm r        -> r
      Unquote r          -> r
      Tactic r _         -> r
      DontCare{}         -> noRange
      Equal r _ _        -> r
      Ellipsis r         -> r
      Generalized e      -> getRange e
      KnownIdent _ q     -> getRange q
      KnownOpApp _ r _ _ _ -> r

-- instance HasRange Telescope where
--     getRange (TeleBind bs) = getRange bs
--     getRange (TeleFun x y) = fuseRange x y

instance HasRange Binder where
  getRange (Binder a b) = fuseRange a b

instance HasRange TypedBinding where
  getRange (TBind r _ _) = r
  getRange (TLet r _)    = r

instance HasRange LamBinding where
  getRange (DomainFree x) = getRange x
  getRange (DomainFull b) = getRange b

instance HasRange BoundName where
  getRange = getRange . boundName

instance HasRange WhereClause where
  getRange  NoWhere               = noRange
  getRange (AnyWhere r ds)        = getRange (r, ds)
  getRange (SomeWhere r e x _ ds) = getRange (r, e, x, ds)

instance HasRange ModuleApplication where
  getRange (SectionApp r _ _) = r
  getRange (RecordModuleInstance r _) = r

instance HasRange a => HasRange (FieldAssignment' a) where
  getRange (FieldAssignment a b) = fuseRange a b

instance HasRange ModuleAssignment where
  getRange (ModuleAssignment a b c) = fuseRange a b `fuseRange` c

instance HasRange RecordDirective where
  getRange (Induction a)          = getRange a
  getRange (Eta a    )            = getRange a
  getRange (Constructor a b)      = getRange (a, b)
  getRange (PatternOrCopattern r) = r

instance HasRange Declaration where
  getRange (TypeSig _ _ x t)       = fuseRange x t
  getRange (FieldSig _ _ x t)      = fuseRange x t
  getRange (Field r _)             = r
  getRange (FunClause lhs rhs wh _) = fuseRange lhs rhs `fuseRange` wh
  getRange (DataSig r _ _ _ _)     = r
  getRange (Data r _ _ _ _ _)      = r
  getRange (DataDef r _ _ _)       = r
  getRange (RecordSig r _ _ _ _)   = r
  getRange (RecordDef r _ _ _ _)   = r
  getRange (Record r _ _ _ _ _ _)  = r
  getRange (RecordDirective r)     = getRange r
  getRange (Mutual r _)            = r
  getRange (InterleavedMutual r _) = r
  getRange (LoneConstructor r _)   = r
  getRange (Abstract r _)          = r
  getRange (Generalize r _)        = r
  getRange (Open r _ _)            = r
  getRange (ModuleMacro r _ _ _ _ _)
                                   = r
  getRange (Import r _ _ _ _)      = r
  getRange (InstanceB r _)         = r
  getRange (Macro r _)             = r
  getRange (Private r _ _)         = r
  getRange (Postulate r _)         = r
  getRange (Primitive r _)         = r
  getRange (Module r _ _ _ _)      = r
  getRange (Infix f _)             = getRange f
  getRange (Syntax n _)            = getRange n
  getRange (PatternSyn r _ _ _)    = r
  getRange (UnquoteDecl r _ _)     = r
  getRange (UnquoteDef r _ _)      = r
  getRange (UnquoteData r _ _ _)   = r
  getRange (Pragma p)              = getRange p
  getRange (Opaque r _)            = r
  getRange (Unfolding r _)         = r

instance HasRange LHS where
  getRange (LHS p eqns ws) = p `fuseRange` eqns `fuseRange` ws

instance HasRange LHSCore where
  getRange (LHSHead f ps)              = fuseRange f ps
  getRange (LHSProj d ps1 lhscore ps2) = d `fuseRange` ps1 `fuseRange` lhscore `fuseRange` ps2
  getRange (LHSWith f wps ps)          = f `fuseRange` wps `fuseRange` ps
  getRange (LHSEllipsis r p)           = r

instance HasRange RHS where
  getRange AbsurdRHS = noRange
  getRange (RHS e)   = getRange e

instance HasRange LamClause where
  getRange (LamClause lhs rhs _) = getRange (lhs, rhs)

instance HasRange DoStmt where
  getRange (DoBind r _ _ _) = r
  getRange (DoThen e)       = getRange e
  getRange (DoLet r _)      = r

instance HasRange Pragma where
  getRange (OptionsPragma r _)               = r
  getRange (BuiltinPragma r _ _)             = r
  getRange (RewritePragma r _ _)             = r
  getRange (CompilePragma r _ _ _)           = r
  getRange (ForeignPragma r _ _)             = r
  getRange (StaticPragma r _)                = r
  getRange (InjectivePragma r _)             = r
  getRange (InlinePragma r _ _)              = r
  getRange (ImpossiblePragma r _)            = r
  getRange (EtaPragma r _)                   = r
  getRange (TerminationCheckPragma r _)      = r
  getRange (NoCoverageCheckPragma r)         = r
  getRange (WarningOnUsage r _ _)            = r
  getRange (WarningOnImport r _)             = r
  getRange (CatchallPragma r)                = r
  getRange (DisplayPragma r _ _)             = r
  getRange (NoPositivityCheckPragma r)       = r
  getRange (PolarityPragma r _ _)            = r
  getRange (NoUniverseCheckPragma r)         = r
  getRange (NotProjectionLikePragma r _)     = r

instance HasRange AsName where
  getRange a = getRange (asRange a, asName a)

instance HasRange Pattern where
  getRange (IdentP _ x)       = getRange x
  getRange (AppP p q)         = fuseRange p q
  getRange (OpAppP r _ _ _)   = r
  getRange (RawAppP r _)      = r
  getRange (ParenP r _)       = r
  getRange (WildP r)          = r
  getRange (AsP r _ _)        = r
  getRange (AbsurdP r)        = r
  getRange (LitP r _)         = r
  getRange (QuoteP r)         = r
  getRange (HiddenP r _)      = r
  getRange (InstanceP r _)    = r
  getRange (DotP r _)         = r
  getRange (RecP r _)         = r
  getRange (EqualP r _)       = r
  getRange (EllipsisP r _)    = r
  getRange (WithP r _)        = r

-- SetRange instances
------------------------------------------------------------------------

instance SetRange Pattern where
  setRange r (IdentP c x)       = IdentP c (setRange r x)
  setRange r (AppP p q)         = AppP (setRange r p) (setRange r q)
  setRange r (OpAppP _ x ns ps) = OpAppP r x ns ps
  setRange r (RawAppP _ ps)     = RawAppP r ps
  setRange r (ParenP _ p)       = ParenP r p
  setRange r (WildP _)          = WildP r
  setRange r (AsP _ x p)        = AsP r (setRange r x) p
  setRange r (AbsurdP _)        = AbsurdP r
  setRange r (LitP _ l)         = LitP r l
  setRange r (QuoteP _)         = QuoteP r
  setRange r (HiddenP _ p)      = HiddenP r p
  setRange r (InstanceP _ p)    = InstanceP r p
  setRange r (DotP _ e)         = DotP r e
  setRange r (RecP _ fs)        = RecP r fs
  setRange r (EqualP _ es)      = EqualP r es
  setRange r (EllipsisP _ mp)   = EllipsisP r mp
  setRange r (WithP _ p)        = WithP r p

instance SetRange TypedBinding where
  setRange r (TBind _ xs e) = TBind r xs e
  setRange r (TLet _ ds)    = TLet r ds

-- KillRange instances
------------------------------------------------------------------------

instance KillRange a => KillRange (FieldAssignment' a) where
  killRange (FieldAssignment a b) = killRangeN FieldAssignment a b

instance KillRange ModuleAssignment where
  killRange (ModuleAssignment a b c) = killRangeN ModuleAssignment a b c

instance KillRange AsName where
  killRange (AsName n _) = killRangeN (flip AsName noRange) n

instance KillRange Binder where
  killRange (Binder a b) = killRangeN Binder a b

instance KillRange BoundName where
  killRange (BName n f t b) = killRangeN BName n f t b

instance KillRange RecordDirective where
  killRange (Induction a)          = killRangeN Induction a
  killRange (Eta a    )            = killRangeN Eta a
  killRange (Constructor a b)      = killRangeN Constructor a b
  killRange (PatternOrCopattern _) = PatternOrCopattern noRange

instance KillRange Declaration where
  killRange (TypeSig i t n e)       = killRangeN (TypeSig i) t n e
  killRange (FieldSig i t n e)      = killRangeN FieldSig i t n e
  killRange (Generalize r ds )      = killRangeN (Generalize noRange) ds
  killRange (Field r fs)            = killRangeN (Field noRange) fs
  killRange (FunClause l r w ca)    = killRangeN FunClause l r w ca
  killRange (DataSig _ er n l e)    = killRangeN (DataSig noRange) er n l e
  killRange (Data _ er n l e c)     = killRangeN (Data noRange) er n l e c
  killRange (DataDef _ n l c)       = killRangeN (DataDef noRange) n l c
  killRange (RecordSig _ er n l e)  = killRangeN (RecordSig noRange) er n l e
  killRange (RecordDef _ n dir k d) = killRangeN (RecordDef noRange) n dir k d
  killRange (RecordDirective a)     = killRangeN RecordDirective a
  killRange (Record _ er n dir k e d)
                                    = killRangeN (Record noRange) er n dir k e d
  killRange (Infix f n)             = killRangeN Infix f n
  killRange (Syntax n no)           = killRangeN (\n -> Syntax n no) n
  killRange (PatternSyn _ n ns p)   = killRangeN (PatternSyn noRange) n ns p
  killRange (Mutual _ d)            = killRangeN (Mutual noRange) d
  killRange (InterleavedMutual _ d) = killRangeN (InterleavedMutual noRange) d
  killRange (LoneConstructor _ d)   = killRangeN (LoneConstructor noRange) d
  killRange (Abstract _ d)          = killRangeN (Abstract noRange) d
  killRange (Private _ o d)         = killRangeN (Private noRange) o d
  killRange (InstanceB _ d)         = killRangeN (InstanceB noRange) d
  killRange (Macro _ d)             = killRangeN (Macro noRange) d
  killRange (Postulate _ t)         = killRangeN (Postulate noRange) t
  killRange (Primitive _ t)         = killRangeN (Primitive noRange) t
  killRange (Open _ q i)            = killRangeN (Open noRange) q i
  killRange (Import _ q a o i)      = killRangeN (\q a -> Import noRange q a o) q a i
  killRange (ModuleMacro _ e n m o i)
                                    = killRangeN
                                        (\e n m -> ModuleMacro noRange e n m o)
                                        e n m i
  killRange (Module _ e q t d)      = killRangeN (Module noRange) e q t d
  killRange (UnquoteDecl _ x t)     = killRangeN (UnquoteDecl noRange) x t
  killRange (UnquoteDef _ x t)      = killRangeN (UnquoteDef noRange) x t
  killRange (UnquoteData _ xs cs t) = killRangeN (UnquoteData noRange) xs cs t
  killRange (Pragma p)              = killRangeN Pragma p
  killRange (Opaque r xs)           = killRangeN Opaque r xs
  killRange (Unfolding r xs)        = killRangeN Unfolding r xs

instance KillRange Expr where
  killRange (Ident q)              = killRangeN Ident q
  killRange (Lit _ l)              = killRangeN (Lit noRange) l
  killRange (QuestionMark _ n)     = QuestionMark noRange n
  killRange (Underscore _ n)       = Underscore noRange n
  killRange (RawApp _ e)           = killRangeN (RawApp noRange) e
  killRange (App _ e a)            = killRangeN (App noRange) e a
  killRange (OpApp _ n ns o)       = killRangeN (OpApp noRange) n ns o
  killRange (WithApp _ e es)       = killRangeN (WithApp noRange) e es
  killRange (HiddenArg _ n)        = killRangeN (HiddenArg noRange) n
  killRange (InstanceArg _ n)      = killRangeN (InstanceArg noRange) n
  killRange (Lam _ l e)            = killRangeN (Lam noRange) l e
  killRange (AbsurdLam _ h)        = killRangeN (AbsurdLam noRange) h
  killRange (ExtendedLam _ e lrw)  = killRangeN (ExtendedLam noRange) e lrw
  killRange (Fun _ e1 e2)          = killRangeN (Fun noRange) e1 e2
  killRange (Pi t e)               = killRangeN Pi t e
  killRange (Rec _ ne)             = killRangeN (Rec noRange) ne
  killRange (RecUpdate _ e ne)     = killRangeN (RecUpdate noRange) e ne
  killRange (Let _ d e)            = killRangeN (Let noRange) d e
  killRange (Paren _ e)            = killRangeN (Paren noRange) e
  killRange (IdiomBrackets _ es)   = killRangeN (IdiomBrackets noRange) es
  killRange (DoBlock _ ss)         = killRangeN (DoBlock noRange) ss
  killRange (Absurd _)             = Absurd noRange
  killRange (As _ n e)             = killRangeN (As noRange) n e
  killRange (Dot _ e)              = killRangeN (Dot noRange) e
  killRange (DoubleDot _ e)        = killRangeN (DoubleDot noRange) e
  killRange (Quote _)              = Quote noRange
  killRange (QuoteTerm _)          = QuoteTerm noRange
  killRange (Unquote _)            = Unquote noRange
  killRange (Tactic _ t)           = killRangeN (Tactic noRange) t
  killRange (DontCare e)           = killRangeN DontCare e
  killRange (Equal _ x y)          = Equal noRange x y
  killRange (Ellipsis _)           = Ellipsis noRange
  killRange (Generalized e)        = killRangeN Generalized e
  killRange (KnownIdent a b)       = killRangeN (KnownIdent a) b
  killRange (KnownOpApp a b c d e) = killRangeN (KnownOpApp a) b c d e

instance KillRange LamBinding where
  killRange (DomainFree b) = killRangeN DomainFree b
  killRange (DomainFull t) = killRangeN DomainFull t

instance KillRange LHS where
  killRange (LHS p r w)  = killRangeN LHS p r w

instance KillRange LamClause where
  killRange (LamClause a b c) = killRangeN LamClause a b c

instance KillRange DoStmt where
  killRange (DoBind r p e w) = killRangeN DoBind r p e w
  killRange (DoThen e)       = killRangeN DoThen e
  killRange (DoLet r ds)     = killRangeN DoLet r ds

instance KillRange ModuleApplication where
  killRange (SectionApp _ t e)    = killRangeN (SectionApp noRange) t e
  killRange (RecordModuleInstance _ q) = killRangeN (RecordModuleInstance noRange) q

instance KillRange e => KillRange (OpApp e) where
  killRange (SyntaxBindingLambda _ l e) = killRangeN (SyntaxBindingLambda noRange) l e
  killRange (Ordinary e)                = killRangeN Ordinary e

instance KillRange Pattern where
  killRange (IdentP c q)      = killRangeN IdentP c q
  killRange (AppP p ps)       = killRangeN AppP p ps
  killRange (RawAppP _ p)     = killRangeN (RawAppP noRange) p
  killRange (OpAppP _ n ns p) = killRangeN (OpAppP noRange) n ns p
  killRange (HiddenP _ n)     = killRangeN (HiddenP noRange) n
  killRange (InstanceP _ n)   = killRangeN (InstanceP noRange) n
  killRange (ParenP _ p)      = killRangeN (ParenP noRange) p
  killRange (WildP _)         = WildP noRange
  killRange (AbsurdP _)       = AbsurdP noRange
  killRange (AsP _ n p)       = killRangeN (AsP noRange) n p
  killRange (DotP _ e)        = killRangeN (DotP noRange) e
  killRange (LitP _ l)        = killRangeN (LitP noRange) l
  killRange (QuoteP _)        = QuoteP noRange
  killRange (RecP _ fs)       = killRangeN (RecP noRange) fs
  killRange (EqualP _ es)     = killRangeN (EqualP noRange) es
  killRange (EllipsisP _ mp)  = killRangeN (EllipsisP noRange) mp
  killRange (WithP _ p)       = killRangeN (WithP noRange) p

instance KillRange Pragma where
  killRange (OptionsPragma _ s)               = OptionsPragma noRange s
  killRange (BuiltinPragma _ s e)             = killRangeN (BuiltinPragma noRange s) e
  killRange (RewritePragma _ _ qs)            = killRangeN (RewritePragma noRange noRange) qs
  killRange (StaticPragma _ q)                = killRangeN (StaticPragma noRange) q
  killRange (InjectivePragma _ q)             = killRangeN (InjectivePragma noRange) q
  killRange (InlinePragma _ b q)              = killRangeN (InlinePragma noRange b) q
  killRange (CompilePragma _ b q s)           = killRangeN (\ q -> CompilePragma noRange b q s) q
  killRange (ForeignPragma _ b s)             = ForeignPragma noRange b s
  killRange (ImpossiblePragma _ strs)         = ImpossiblePragma noRange strs
  killRange (TerminationCheckPragma _ t)      = TerminationCheckPragma noRange (killRange t)
  killRange (NoCoverageCheckPragma _)         = NoCoverageCheckPragma noRange
  killRange (WarningOnUsage _ nm str)         = WarningOnUsage noRange (killRange nm) str
  killRange (WarningOnImport _ str)           = WarningOnImport noRange str
  killRange (CatchallPragma _)                = CatchallPragma noRange
  killRange (DisplayPragma _ lhs rhs)         = killRangeN (DisplayPragma noRange) lhs rhs
  killRange (EtaPragma _ q)                   = killRangeN (EtaPragma noRange) q
  killRange (NoPositivityCheckPragma _)       = NoPositivityCheckPragma noRange
  killRange (PolarityPragma _ q occs)         = killRangeN (\q -> PolarityPragma noRange q occs) q
  killRange (NoUniverseCheckPragma _)         = NoUniverseCheckPragma noRange
  killRange (NotProjectionLikePragma _ q)     = NotProjectionLikePragma noRange q

instance KillRange RHS where
  killRange AbsurdRHS = AbsurdRHS
  killRange (RHS e)   = killRangeN RHS e

instance KillRange TypedBinding where
  killRange (TBind _ b e) = killRangeN (TBind noRange) b e
  killRange (TLet r ds)   = killRangeN TLet r ds

instance KillRange WhereClause where
  killRange NoWhere               = NoWhere
  killRange (AnyWhere r d)        = killRangeN (AnyWhere noRange) d
  killRange (SomeWhere r e n a d) =
    killRangeN (SomeWhere noRange) e n a d

------------------------------------------------------------------------
-- NFData instances

-- | Ranges are not forced.

instance NFData Expr where
  rnf (Ident a)           = rnf a
  rnf (Lit _ a)           = rnf a
  rnf (QuestionMark _ a)  = rnf a
  rnf (Underscore _ a)    = rnf a
  rnf (RawApp _ a)        = rnf a
  rnf (App _ a b)         = rnf a `seq` rnf b
  rnf (OpApp _ a b c)     = rnf a `seq` rnf b `seq` rnf c
  rnf (WithApp _ a b)     = rnf a `seq` rnf b
  rnf (HiddenArg _ a)     = rnf a
  rnf (InstanceArg _ a)   = rnf a
  rnf (Lam _ a b)         = rnf a `seq` rnf b
  rnf (AbsurdLam _ a)     = rnf a
  rnf (ExtendedLam _ a b) = rnf a `seq` rnf b
  rnf (Fun _ a b)         = rnf a `seq` rnf b
  rnf (Pi a b)            = rnf a `seq` rnf b
  rnf (Rec _ a)           = rnf a
  rnf (RecUpdate _ a b)   = rnf a `seq` rnf b
  rnf (Let _ a b)         = rnf a `seq` rnf b
  rnf (Paren _ a)         = rnf a
  rnf (IdiomBrackets _ a) = rnf a
  rnf (DoBlock _ a)       = rnf a
  rnf (Absurd _)          = ()
  rnf (As _ a b)          = rnf a `seq` rnf b
  rnf (Dot _ a)           = rnf a
  rnf (DoubleDot _ a)     = rnf a
  rnf (Quote _)           = ()
  rnf (QuoteTerm _)       = ()
  rnf (Tactic _ a)        = rnf a
  rnf (Unquote _)         = ()
  rnf (DontCare a)        = rnf a
  rnf (Equal _ a b)       = rnf a `seq` rnf b
  rnf (Ellipsis _)        = ()
  rnf (Generalized e)     = rnf e
  rnf (KnownIdent a b)    = rnf b
  rnf (KnownOpApp a b c d e) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf c

-- | Ranges are not forced.

instance NFData Pattern where
  rnf (IdentP a b)     = rnf a `seq` rnf b
  rnf (QuoteP _)       = ()
  rnf (AppP a b)       = rnf a `seq` rnf b
  rnf (RawAppP _ a)    = rnf a
  rnf (OpAppP _ a b c) = rnf a `seq` rnf b `seq` rnf c
  rnf (HiddenP _ a)    = rnf a
  rnf (InstanceP _ a)  = rnf a
  rnf (ParenP _ a)     = rnf a
  rnf (WildP _)        = ()
  rnf (AbsurdP _)      = ()
  rnf (AsP _ a b)      = rnf a `seq` rnf b
  rnf (DotP _ a)       = rnf a
  rnf (LitP _ a)       = rnf a
  rnf (RecP _ a)       = rnf a
  rnf (EqualP _ es)    = rnf es
  rnf (EllipsisP _ mp) = rnf mp
  rnf (WithP _ a)      = rnf a

-- | Ranges are not forced.

instance NFData RecordDirective where
  rnf (Induction a)          = rnf a
  rnf (Eta a    )            = rnf a
  rnf (Constructor a b)      = rnf (a, b)
  rnf (PatternOrCopattern _) = ()

instance NFData Declaration where
  rnf (TypeSig a b c d)       = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (FieldSig a b c d)      = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (Generalize _ a)        = rnf a
  rnf (Field _ fs)            = rnf fs
  rnf (FunClause a b c d)     = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (DataSig _ a b c d)     = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (Data _ a b c d e)      = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
                                      `seq` rnf e
  rnf (DataDef _ a b c)       = rnf a `seq` rnf b `seq` rnf c
  rnf (RecordSig _ a b c d)   = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (RecordDef _ a b c d)   = rnf (a, b, c, d)
  rnf (Record _ a b c d e f)  = rnf (a, b, c, d, e, f)
  rnf (RecordDirective a)     = rnf a
  rnf (Infix a b)             = rnf a `seq` rnf b
  rnf (Syntax a b)            = rnf a `seq` rnf b
  rnf (PatternSyn _ a b c)    = rnf a `seq` rnf b `seq` rnf c
  rnf (Mutual _ a)            = rnf a
  rnf (InterleavedMutual _ a) = rnf a
  rnf (LoneConstructor _ a)   = rnf a
  rnf (Abstract _ a)          = rnf a
  rnf (Private _ _ a)         = rnf a
  rnf (InstanceB _ a)         = rnf a
  rnf (Macro _ a)             = rnf a
  rnf (Postulate _ a)         = rnf a
  rnf (Primitive _ a)         = rnf a
  rnf (Open _ a b)            = rnf a `seq` rnf b
  rnf (Import _ a b _ c)      = rnf a `seq` rnf b `seq` rnf c
  rnf (ModuleMacro _ a b c _ d)
                              = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (Module _ a b c d)      = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
  rnf (UnquoteDecl _ a b)     = rnf a `seq` rnf b
  rnf (UnquoteDef _ a b)      = rnf a `seq` rnf b
  rnf (UnquoteData _ a b c)   = rnf a `seq` rnf b `seq` rnf c
  rnf (Pragma a)              = rnf a
  rnf (Opaque r xs)           = rnf r `seq` rnf xs
  rnf (Unfolding r xs)        = rnf r `seq` rnf xs

instance NFData OpenShortHand

-- | Ranges are not forced.

instance NFData Pragma where
  rnf (OptionsPragma _ a)               = rnf a
  rnf (BuiltinPragma _ a b)             = rnf a `seq` rnf b
  rnf (RewritePragma _ _ a)             = rnf a
  rnf (CompilePragma _ a b c)           = rnf a `seq` rnf b `seq` rnf c
  rnf (ForeignPragma _ b s)             = rnf b `seq` rnf s
  rnf (StaticPragma _ a)                = rnf a
  rnf (InjectivePragma _ a)             = rnf a
  rnf (InlinePragma _ _ a)              = rnf a
  rnf (ImpossiblePragma _ a)            = rnf a
  rnf (EtaPragma _ a)                   = rnf a
  rnf (TerminationCheckPragma _ a)      = rnf a
  rnf (NoCoverageCheckPragma _)         = ()
  rnf (WarningOnUsage _ a b)            = rnf a `seq` rnf b
  rnf (WarningOnImport _ a)             = rnf a
  rnf (CatchallPragma _)                = ()
  rnf (DisplayPragma _ a b)             = rnf a `seq` rnf b
  rnf (NoPositivityCheckPragma _)       = ()
  rnf (PolarityPragma _ a b)            = rnf a `seq` rnf b
  rnf (NoUniverseCheckPragma _)         = ()
  rnf (NotProjectionLikePragma _ q)     = rnf q

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
  rnf NoWhere               = ()
  rnf (AnyWhere _ a)        = rnf a
  rnf (SomeWhere _ a b c d) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d

instance NFData LamClause where
  rnf (LamClause a b c) = rnf (a, b, c)

instance NFData a => NFData (LamBinding' a) where
  rnf (DomainFree a) = rnf a
  rnf (DomainFull a) = rnf a

instance NFData Binder where
  rnf (Binder a b) = rnf a `seq` rnf b

instance NFData BoundName where
  rnf (BName a b c d) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d

instance NFData a => NFData (RHS' a) where
  rnf AbsurdRHS = ()
  rnf (RHS a)   = rnf a

instance NFData DoStmt where
  rnf (DoBind _ p e w) = rnf (p, e, w)
  rnf (DoThen e)       = rnf e
  rnf (DoLet _ ds)     = rnf ds
