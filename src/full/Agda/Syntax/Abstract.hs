{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Agda.Syntax.Internal").
-}
module Agda.Syntax.Abstract
    ( module Agda.Syntax.Abstract
    , module Agda.Syntax.Abstract.Name
    ) where

import Prelude
import Control.Arrow (first)--, second, (***))

import Data.Foldable (Foldable)
import qualified Data.Foldable as Fold
import Data.Function (on)
import Data.Map (Map)
import Data.Maybe
import Data.Sequence (Seq, (<|), (><))
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Void
import Data.Data (Data)
import Data.Monoid (mappend)

import Agda.Syntax.Concrete (FieldAssignment'(..), exprFieldA)--, HoleContent'(..))
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Abstract.Name as A (QNamed)
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.Geniplate
import Agda.Utils.Lens
import Agda.Utils.Pretty

import Agda.Utils.Impossible

-- | A name in a binding position: we also compare the nameConcrete
-- when comparing the binders for equality.
--
-- With @--caching@ on we compare abstract syntax to determine if we can
-- reuse previous typechecking results: during that comparison two
-- names can have the same nameId but be semantically different,
-- e.g. in @{_ : A} -> ..@ vs. @{r : A} -> ..@.

newtype BindName = BindName { unBind :: Name }
  deriving (Show, Data, HasRange, KillRange, SetRange)

mkBindName :: Name -> BindName
mkBindName x = BindName x

instance Eq BindName where
  BindName n == BindName m
    = ((==) `on` nameId) n m
      && ((==) `on` nameConcrete) n m

instance Ord BindName where
  BindName n `compare` BindName m
    = (compare `on` nameId) n m
      `mappend` (compare `on` nameConcrete) n m

type Args = [NamedArg Expr]

-- | Expressions after scope checking (operators parsed, names resolved).
data Expr
  = Var  Name                          -- ^ Bound variable.
  | Def  QName                         -- ^ Constant: axiom, function, data or record type.
  | Proj ProjOrigin AmbiguousQName     -- ^ Projection (overloaded).
  | Con  AmbiguousQName                -- ^ Constructor (overloaded).
  | PatternSyn AmbiguousQName          -- ^ Pattern synonym.
  | Macro QName                        -- ^ Macro.
  | Lit Literal                        -- ^ Literal.
  | QuestionMark MetaInfo InteractionId
    -- ^ Meta variable for interaction.
    --   The 'InteractionId' is usually identical with the
    --   'metaNumber' of 'MetaInfo'.
    --   However, if you want to print an interaction meta as
    --   just @?@ instead of @?n@, you should set the
    --   'metaNumber' to 'Nothing' while keeping the 'InteractionId'.
  | Underscore   MetaInfo
    -- ^ Meta variable for hidden argument (must be inferred locally).
  | Dot ExprInfo Expr                  -- ^ @.e@, for postfix projection.
  | App  AppInfo Expr (NamedArg Expr)  -- ^ Ordinary (binary) application.
  | WithApp ExprInfo Expr [Expr]       -- ^ With application.
  | Lam  ExprInfo LamBinding Expr      -- ^ @λ bs → e@.
  | AbsurdLam ExprInfo Hiding          -- ^ @λ()@ or @λ{}@.
  | ExtendedLam ExprInfo DefInfo QName [Clause]
  | Pi   ExprInfo Telescope Expr       -- ^ Dependent function space @Γ → A@.
  | Generalized (Set.Set QName) Expr   -- ^ Like a Pi, but the ordering is not known
  | Fun  ExprInfo (Arg Expr) Expr      -- ^ Non-dependent function space.
  | Set  ExprInfo Integer              -- ^ @Set@, @Set1@, @Set2@, ...
  | Prop ExprInfo Integer              -- ^ @Prop@, @Prop1@, @Prop2@, ...
  | Let  ExprInfo [LetBinding] Expr    -- ^ @let bs in e@.
  | ETel Telescope                     -- ^ Only used when printing telescopes.
  | Rec  ExprInfo RecordAssigns        -- ^ Record construction.
  | RecUpdate ExprInfo Expr Assigns    -- ^ Record update.
  | ScopedExpr ScopeInfo Expr          -- ^ Scope annotation.
  | Quote ExprInfo                     -- ^ Quote an identifier 'QName'.
  | QuoteTerm ExprInfo                 -- ^ Quote a term.
  | Unquote ExprInfo                   -- ^ The splicing construct: unquote ...
  | Tactic ExprInfo Expr [NamedArg Expr]
                                       -- ^ @tactic e x1 .. xn@
  | DontCare Expr                      -- ^ For printing @DontCare@ from @Syntax.Internal@.
  deriving (Data, Show)

-- | Smart constructor for Generalized
generalized :: Set.Set QName -> Expr -> Expr
generalized s e
    | Set.null s = e
    | otherwise = Generalized s e

-- | Record field assignment @f = e@.
type Assign  = FieldAssignment' Expr
type Assigns = [Assign]
type RecordAssign  = Either Assign ModuleName
type RecordAssigns = [RecordAssign]

-- | Is a type signature a `postulate' or a function signature?
data Axiom
  = FunSig    -- ^ A function signature.
  | NoFunSig  -- ^ Not a function signature, i.e., a postulate (in user input)
              --   or another (e.g. data/record) type signature (internally).
  deriving (Data, Eq, Ord, Show)

-- | Renaming (generic).
type Ren a = [(a, a)]

data ScopeCopyInfo = ScopeCopyInfo
  { renModules :: Ren ModuleName
  , renNames   :: Ren QName }
  deriving (Eq, Show, Data)

initCopyInfo :: ScopeCopyInfo
initCopyInfo = ScopeCopyInfo
  { renModules = []
  , renNames   = []
  }

instance Pretty ScopeCopyInfo where
  pretty i = vcat [ prRen "renModules =" (renModules i)
                  , prRen "renNames   =" (renNames i) ]
    where
      prRen s r = sep [ text s, nest 2 $ vcat (map pr r) ]
      pr (x, y) = pretty x <+> "->" <+> pretty y

data Declaration
  = Axiom      Axiom DefInfo ArgInfo (Maybe [Occurrence]) QName Expr
    -- ^ Type signature (can be irrelevant, but not hidden).
    --
    -- The fourth argument contains an optional assignment of
    -- polarities to arguments.
  | Generalize (Set.Set QName) DefInfo ArgInfo QName Expr
    -- ^ First argument is set of generalizable variables used in the type.
  | Field      DefInfo QName (Arg Expr)              -- ^ record field
  | Primitive  DefInfo QName Expr                    -- ^ primitive function
  | Mutual     MutualInfo [Declaration]              -- ^ a bunch of mutually recursive definitions
  | Section    ModuleInfo ModuleName GeneralizeTelescope [Declaration]
  | Apply      ModuleInfo ModuleName ModuleApplication ScopeCopyInfo ImportDirective
    -- ^ The @ImportDirective@ is for highlighting purposes.
  | Import     ModuleInfo ModuleName ImportDirective
    -- ^ The @ImportDirective@ is for highlighting purposes.
  | Pragma     Range      Pragma
  | Open       ModuleInfo ModuleName ImportDirective
    -- ^ only retained for highlighting purposes
  | FunDef     DefInfo QName Delayed [Clause] -- ^ sequence of function clauses
  | DataSig    DefInfo QName GeneralizeTelescope Expr -- ^ lone data signature
  | DataDef    DefInfo QName UniverseCheck DataDefParams [Constructor]
      -- ^ the 'LamBinding's are 'DomainFree' and bind the parameters of the datatype.
  | RecSig     DefInfo QName GeneralizeTelescope Expr -- ^ lone record signature
  | RecDef     DefInfo QName UniverseCheck (Maybe (Ranged Induction)) (Maybe HasEta) (Maybe QName) DataDefParams Expr [Declaration]
      -- ^ The 'LamBinding's are 'DomainFree' and bind the parameters of the datatype.
      --   The 'Expr' gives the constructor type telescope, @(x1 : A1)..(xn : An) -> Prop@,
      --   and the optional name is the constructor's name.
  | PatternSynDef QName [Arg Name] (Pattern' Void)
      -- ^ Only for highlighting purposes
  | UnquoteDecl MutualInfo [DefInfo] [QName] Expr
  | UnquoteDef  [DefInfo] [QName] Expr
  | ScopedDecl ScopeInfo [Declaration]  -- ^ scope annotation
  deriving (Data, Show)

type DefInfo = DefInfo' Expr

type ImportDirective = ImportDirective' QName ModuleName
type Renaming        = Renaming'        QName ModuleName
type ImportedName    = ImportedName'    QName ModuleName

data ModuleApplication
    = SectionApp Telescope ModuleName [NamedArg Expr]
      -- ^ @tel. M args@:  applies @M@ to @args@ and abstracts @tel@.
    | RecordModuleInstance ModuleName
      -- ^ @M {{...}}@
  deriving (Data, Show, Eq)

data Pragma
  = OptionsPragma [String]
  | BuiltinPragma String ResolvedName
    -- ^ 'ResolvedName' is not 'UnknownName'.
    --   Name can be ambiguous e.g. for built-in constructors.
  | BuiltinNoDefPragma String QName
    -- ^ Builtins that do not come with a definition,
    --   but declare a name for an Agda concept.
  | RewritePragma [QName]
  | CompilePragma String QName String
  | StaticPragma QName
  | EtaPragma QName
    -- ^ For coinductive records, use pragma instead of regular
    --   @eta-equality@ definition (as it is might make Agda loop).
  | InjectivePragma QName
  | InlinePragma Bool QName -- INLINE or NOINLINE
  | DisplayPragma QName [NamedArg Pattern] Expr
  deriving (Data, Show, Eq)

-- | Bindings that are valid in a @let@.
data LetBinding
  = LetBind LetInfo ArgInfo BindName Expr Expr
    -- ^ @LetBind info rel name type defn@
  | LetPatBind LetInfo Pattern Expr
    -- ^ Irrefutable pattern binding.
  | LetApply ModuleInfo ModuleName ModuleApplication ScopeCopyInfo ImportDirective
    -- ^ @LetApply mi newM (oldM args) renamings dir@.
    -- The @ImportDirective@ is for highlighting purposes.
  | LetOpen ModuleInfo ModuleName ImportDirective
    -- ^ only for highlighting and abstractToConcrete
  | LetDeclaredVariable BindName
    -- ^ Only used for highlighting. Refers to the first occurrence of
    -- @x@ in @let x : A; x = e@.
--  | LetGeneralize DefInfo ArgInfo Expr
  deriving (Data, Show, Eq)


-- | Only 'Axiom's.
type TypeSignature  = Declaration
type Constructor    = TypeSignature
type Field          = TypeSignature

type TacticAttr = Maybe Expr

-- A Binder @x\@p@, the pattern is optional
data Binder' a = Binder
  { binderPattern :: Maybe Pattern
  , binderName    :: a
  } deriving (Data, Show, Eq, Functor, Foldable, Traversable)

type Binder = Binder' BindName

mkBinder :: a -> Binder' a
mkBinder = Binder Nothing

mkBinder_ :: Name -> Binder
mkBinder_ = mkBinder . mkBindName

extractPattern :: Binder' a -> Maybe (Pattern, a)
extractPattern (Binder p a) = (,a) <$> p

-- | A lambda binding is either domain free or typed.
data LamBinding
  = DomainFree TacticAttr (NamedArg Binder)
    -- ^ . @x@ or @{x}@ or @.x@ or @{x = y}@ or @x\@p@ or @(p)@
  | DomainFull TypedBinding
    -- ^ . @(xs:e)@ or @{xs:e}@ or @(let Ds)@
  deriving (Data, Show, Eq)

mkDomainFree :: NamedArg Binder -> LamBinding
mkDomainFree = DomainFree Nothing

-- | A typed binding.  Appears in dependent function spaces, typed lambdas, and
--   telescopes.  It might be tempting to simplify this to only bind a single
--   name at a time, and translate, say, @(x y : A)@ to @(x : A)(y : A)@
--   before type-checking.  However, this would be slightly problematic:
--
--     1. We would have to typecheck the type @A@ several times.
--
--     2. If @A@ contains a meta variable or hole, it would be duplicated
--        by such a translation.
--
--   While 1. is only slightly inefficient, 2. would be an outright bug.
--   Duplicating @A@ could not be done naively, we would have to make sure
--   that the metas of the copy are aliases of the metas of the original.

data TypedBinding
  = TBind Range TacticAttr [NamedArg Binder] Expr
    -- ^ As in telescope @(x y z : A)@ or type @(x y z : A) -> B@.
  | TLet Range [LetBinding]
    -- ^ E.g. @(let x = e)@ or @(let open M)@.
  deriving (Data, Show, Eq)

mkTBind :: Range -> [NamedArg Binder] -> Expr -> TypedBinding
mkTBind r = TBind r Nothing

type Telescope  = [TypedBinding]

data GeneralizeTelescope = GeneralizeTel
  { generalizeTelVars :: Map QName Name
    -- ^ Maps generalize variables to the corresponding bound variable (to be
    --   introduced by the generalisation).
  , generalizeTel     :: Telescope }
  deriving (Data, Show, Eq)

data DataDefParams = DataDefParams
  { dataDefGeneralizedParams :: Set Name
    -- ^ We don't yet know the position of generalized parameters from the data
    --   sig, so we keep these in a set on the side.
  , dataDefParams :: [LamBinding]
  }
  deriving (Data, Show, Eq)

noDataDefParams :: DataDefParams
noDataDefParams = DataDefParams Set.empty []

-- | A user pattern together with an internal term that it should be equal to
--   after splitting is complete.
--   Special cases:
--    * User pattern is a variable but internal term isn't:
--      this will be turned into an as pattern.
--    * User pattern is a dot pattern:
--      this pattern won't trigger any splitting but will be checked
--      for equality after all splitting is complete and as patterns have
--      been bound.
--    * User pattern is an absurd pattern:
--      emptiness of the type will be checked after splitting is complete.
data ProblemEq = ProblemEq
  { problemInPat :: Pattern
  , problemInst  :: I.Term
  , problemType  :: I.Dom I.Type
  } deriving (Data, Show)

-- These are not relevant for caching purposes
instance Eq ProblemEq where _ == _ = True

-- | We could throw away @where@ clauses at this point and translate them to
--   @let@. It's not obvious how to remember that the @let@ was really a
--   @where@ clause though, so for the time being we keep it here.
data Clause' lhs = Clause
  { clauseLHS        :: lhs
  , clauseStrippedPats :: [ProblemEq]
      -- ^ Only in with-clauses where we inherit some already checked patterns from the parent.
      --   These live in the context of the parent clause left-hand side.
  , clauseRHS        :: RHS
  , clauseWhereDecls :: WhereDeclarations
  , clauseCatchall   :: Bool
  } deriving (Data, Show, Functor, Foldable, Traversable, Eq)

data WhereDeclarations = WhereDecls
  { whereModule :: Maybe ModuleName
  , whereDecls  :: [Declaration]
  } deriving (Data, Show, Eq)

noWhereDecls :: WhereDeclarations
noWhereDecls = WhereDecls Nothing []

type Clause = Clause' LHS
type SpineClause = Clause' SpineLHS
type RewriteEqn  = RewriteEqn' QName Pattern Expr

data RHS
  = RHS
    { rhsExpr     :: Expr
    , rhsConcrete :: Maybe C.Expr
      -- ^ We store the original concrete expression in case
      --   we have to reproduce it during interactive case splitting.
      --   'Nothing' for internally generated rhss.
    }
  | AbsurdRHS
  | WithRHS QName [WithHiding Expr] [Clause]
      -- ^ The 'QName' is the name of the with function.
  | RewriteRHS
    { rewriteExprs      :: [RewriteEqn]
      -- ^ The 'QName's are the names of the generated with functions,
      --   one for each 'Expr'.
    , rewriteStrippedPats :: [ProblemEq]
      -- ^ The patterns stripped by with-desugaring. These are only present
      --   if this rewrite follows a with.
    , rewriteRHS        :: RHS
      -- ^ The RHS should not be another @RewriteRHS@.
    , rewriteWhereDecls :: WhereDeclarations
      -- ^ The where clauses are attached to the @RewriteRHS@ by
      ---  the scope checker (instead of to the clause).
    }
  deriving (Data, Show)

-- | Ignore 'rhsConcrete' when comparing 'RHS's.
instance Eq RHS where
  RHS e _          == RHS e' _            = e == e'
  AbsurdRHS        == AbsurdRHS           = True
  WithRHS a b c    == WithRHS a' b' c'    = and [ a == a', b == b', c == c' ]
  RewriteRHS a b c d == RewriteRHS a' b' c' d' = and [ a == a', b == b', c == c' , d == d' ]
  _                == _                   = False

-- | The lhs of a clause in spine view (inside-out).
--   Projection patterns are contained in @spLhsPats@,
--   represented as @ProjP d@.
data SpineLHS = SpineLHS
  { spLhsInfo     :: LHSInfo             -- ^ Range.
  , spLhsDefName  :: QName               -- ^ Name of function we are defining.
  , spLhsPats     :: [NamedArg Pattern]  -- ^ Elimination by pattern, projections, with-patterns.
  }
  deriving (Data, Show, Eq)

-- | Ignore 'Range' when comparing 'LHS's.
instance Eq LHS where
  LHS _ core == LHS _ core' = core == core'

-- | The lhs of a clause in focused (projection-application) view (outside-in).
--   Projection patters are represented as 'LHSProj's.
data LHS = LHS
  { lhsInfo     :: LHSInfo               -- ^ Range.
  , lhsCore     :: LHSCore               -- ^ Copatterns.
  }
  deriving (Data, Show)

-- | The lhs in projection-application and with-pattern view.
--   Parameterised over the type @e@ of dot patterns.
data LHSCore' e
    -- | The head applied to ordinary patterns.
  = LHSHead  { lhsDefName  :: QName
                 -- ^ Head @f@.
             , lhsPats     :: [NamedArg (Pattern' e)]
                 -- ^ Applied to patterns @ps@.
             }
    -- | Projection.
  | LHSProj  { lhsDestructor :: AmbiguousQName
                 -- ^ Record projection identifier.
             , lhsFocus      :: NamedArg (LHSCore' e)
                 -- ^ Main argument of projection.
             , lhsPats       :: [NamedArg (Pattern' e)]
                 -- ^ Further applied to patterns.
             }
    -- | With patterns.
  | LHSWith  { lhsHead         :: LHSCore' e
                 -- ^ E.g. the 'LHSHead'.
             , lhsWithPatterns :: [Pattern' e]
                 -- ^ Applied to with patterns @| p1 | ... | pn@.
                 --   These patterns are not prefixed with @WithP@!
             , lhsPats         :: [NamedArg (Pattern' e)]
                 -- ^ Further applied to patterns.
             }
  deriving (Data, Show, Functor, Foldable, Traversable, Eq)

type LHSCore = LHSCore' Expr

---------------------------------------------------------------------------
-- * Patterns
---------------------------------------------------------------------------

-- | Parameterised over the type of dot patterns.
data Pattern' e
  = VarP BindName
  | ConP ConPatInfo AmbiguousQName (NAPs e)
  | ProjP PatInfo ProjOrigin AmbiguousQName
    -- ^ Destructor pattern @d@.
  | DefP PatInfo AmbiguousQName (NAPs e)
    -- ^ Defined pattern: function definition @f ps@.
    --   It is also abused to convert destructor patterns into concrete syntax
    --   thus, we put AmbiguousQName here as well.
  | WildP PatInfo
    -- ^ Underscore pattern entered by user.
    --   Or generated at type checking for implicit arguments.
  | AsP PatInfo BindName (Pattern' e)
  | DotP PatInfo e
    -- ^ Dot pattern @.e@
  | AbsurdP PatInfo
  | LitP Literal
  | PatternSynP PatInfo AmbiguousQName (NAPs e)
  | RecP PatInfo [FieldAssignment' (Pattern' e)]
  | EqualP PatInfo [(e, e)]
  | WithP PatInfo (Pattern' e)  -- ^ @| p@, for with-patterns.
  deriving (Data, Show, Functor, Foldable, Traversable, Eq)

type NAPs e   = [NamedArg (Pattern' e)]
type Pattern  = Pattern' Expr
type Patterns = [NamedArg Pattern]

instance IsProjP (Pattern' e) where
  -- Andreas, 2018-06-19, issue #3130
  -- Do not interpret things like .(p) as projection pattern any more.
  -- maybePostfixProjP (DotP _ e)    = isProjP e <&> \ (_o, d) -> (ProjPostfix, d)
  isProjP (ProjP _ o d) = Just (o, d)
  isProjP _ = Nothing

instance IsProjP Expr where
  isProjP (Proj o ds)      = Just (o, ds)
  isProjP (ScopedExpr _ e) = isProjP e
  isProjP _ = Nothing

{--------------------------------------------------------------------------
    Things we parse but are not part of the Agda file syntax
 --------------------------------------------------------------------------}

type HoleContent = C.HoleContent' () Pattern Expr

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

-- | Does not compare 'ScopeInfo' fields.
--   Does not distinguish between prefix and postfix projections.

instance Eq Expr where
  ScopedExpr _ a1         == ScopedExpr _ a2         = a1 == a2

  Var a1                  == Var a2                  = a1 == a2
  Def a1                  == Def a2                  = a1 == a2
  Proj _ a1               == Proj _ a2               = a1 == a2
  Con a1                  == Con a2                  = a1 == a2
  PatternSyn a1           == PatternSyn a2           = a1 == a2
  Macro a1                == Macro a2                = a1 == a2
  Lit a1                  == Lit a2                  = a1 == a2
  QuestionMark a1 b1      == QuestionMark a2 b2      = (a1, b1) == (a2, b2)
  Underscore a1           == Underscore a2           = a1 == a2
  Dot r1 e1               == Dot r2 e2               = (r1, e1) == (r2, e2)
  App a1 b1 c1            == App a2 b2 c2            = (a1, b1, c1) == (a2, b2, c2)
  WithApp a1 b1 c1        == WithApp a2 b2 c2        = (a1, b1, c1) == (a2, b2, c2)
  Lam a1 b1 c1            == Lam a2 b2 c2            = (a1, b1, c1) == (a2, b2, c2)
  AbsurdLam a1 b1         == AbsurdLam a2 b2         = (a1, b1) == (a2, b2)
  ExtendedLam a1 b1 c1 d1 == ExtendedLam a2 b2 c2 d2 = (a1, b1, c1, d1) == (a2, b2, c2, d2)
  Pi a1 b1 c1             == Pi a2 b2 c2             = (a1, b1, c1) == (a2, b2, c2)
  Generalized a1 b1       == Generalized a2 b2       = (a1, b1) == (a2, b2)
  Fun a1 b1 c1            == Fun a2 b2 c2            = (a1, b1, c1) == (a2, b2, c2)
  Set a1 b1               == Set a2 b2               = (a1, b1) == (a2, b2)
  Prop a1 b1              == Prop a2 b2              = (a1, b1) == (a2, b2)
  Let a1 b1 c1            == Let a2 b2 c2            = (a1, b1, c1) == (a2, b2, c2)
  ETel a1                 == ETel a2                 = a1 == a2
  Rec a1 b1               == Rec a2 b2               = (a1, b1) == (a2, b2)
  RecUpdate a1 b1 c1      == RecUpdate a2 b2 c2      = (a1, b1, c1) == (a2, b2, c2)
  Quote a1                == Quote a2                = a1 == a2
  QuoteTerm a1            == QuoteTerm a2            = a1 == a2
  Unquote a1              == Unquote a2              = a1 == a2
  Tactic a1 b1 c1         == Tactic a2 b2 c2         = (a1, b1, c1) == (a2, b2, c2)
  DontCare a1             == DontCare a2             = a1 == a2

  _                       == _                       = False

-- | Does not compare 'ScopeInfo' fields.

instance Eq Declaration where
  ScopedDecl _ a1                == ScopedDecl _ a2                = a1 == a2

  Axiom a1 b1 c1 d1 e1 f1        == Axiom a2 b2 c2 d2 e2 f2        = (a1, b1, c1, d1, e1, f1) == (a2, b2, c2, d2, e2, f2)
  Generalize a1 b1 c1 d1 e1      == Generalize a2 b2 c2 d2 e2      = (a1, b1, c1, d1, e1) == (a2, b2, c2, d2, e2)
  Field a1 b1 c1                 == Field a2 b2 c2                 = (a1, b1, c1) == (a2, b2, c2)
  Primitive a1 b1 c1             == Primitive a2 b2 c2             = (a1, b1, c1) == (a2, b2, c2)
  Mutual a1 b1                   == Mutual a2 b2                   = (a1, b1) == (a2, b2)
  Section a1 b1 c1 d1            == Section a2 b2 c2 d2            = (a1, b1, c1, d1) == (a2, b2, c2, d2)
  Apply a1 b1 c1 d1 e1           == Apply a2 b2 c2 d2 e2           = (a1, b1, c1, d1, e1) == (a2, b2, c2, d2, e2)
  Import a1 b1 c1                == Import a2 b2 c2                = (a1, b1, c1) == (a2, b2, c2)
  Pragma a1 b1                   == Pragma a2 b2                   = (a1, b1) == (a2, b2)
  Open a1 b1 c1                  == Open a2 b2 c2                  = (a1, b1, c1) == (a2, b2, c2)
  FunDef a1 b1 c1 d1             == FunDef a2 b2 c2 d2             = (a1, b1, c1, d1) == (a2, b2, c2, d2)
  DataSig a1 b1 c1 d1            == DataSig a2 b2 c2 d2            = (a1, b1, c1, d1) == (a2, b2, c2, d2)
  DataDef a1 b1 c1 d1 e1         == DataDef a2 b2 c2 d2 e2         = (a1, b1, c1, d1, e1) == (a2, b2, c2, d2, e2)
  RecSig a1 b1 c1 d1             == RecSig a2 b2 c2 d2             = (a1, b1, c1, d1) == (a2, b2, c2, d2)
  RecDef a1 b1 c1 d1 e1 f1 g1 h1 i1 == RecDef a2 b2 c2 d2 e2 f2 g2 h2 i2 = (a1, b1, c1, d1, e1, f1, g1, h1, i1) == (a2, b2, c2, d2, e2, f2, g2, h2, i2)
  PatternSynDef a1 b1 c1         == PatternSynDef a2 b2 c2         = (a1, b1, c1) == (a2, b2, c2)
  UnquoteDecl a1 b1 c1 d1        == UnquoteDecl a2 b2 c2 d2        = (a1, b1, c1, d1) == (a2, b2, c2, d2)
  UnquoteDef a1 b1 c1            == UnquoteDef a2 b2 c2            = (a1, b1, c1) == (a2, b2, c2)

  _                              == _                              = False

instance Underscore Expr where
  underscore   = Underscore emptyMetaInfo
  isUnderscore = __IMPOSSIBLE__

instance LensHiding LamBinding where
  getHiding   (DomainFree _ x) = getHiding x
  getHiding   (DomainFull tb)  = getHiding tb
  mapHiding f (DomainFree t x) = DomainFree t $ mapHiding f x
  mapHiding f (DomainFull tb)  = DomainFull $ mapHiding f tb

instance LensHiding TypedBinding where
  getHiding (TBind _ _ (x : _) _) = getHiding x   -- Slightly dubious
  getHiding (TBind _ _ [] _)      = __IMPOSSIBLE__
  getHiding TLet{}                = mempty
  mapHiding f (TBind r t xs e)    = TBind r t ((map . mapHiding) f xs) e
  mapHiding f b@TLet{}            = b

instance HasRange a => HasRange (Binder' a) where
  getRange (Binder p n) = fuseRange p n

instance HasRange LamBinding where
    getRange (DomainFree _ x) = getRange x
    getRange (DomainFull b)   = getRange b

instance HasRange TypedBinding where
    getRange (TBind r _ _ _) = r
    getRange (TLet r _)    = r

instance HasRange Expr where
    getRange (Var x)               = getRange x
    getRange (Def x)               = getRange x
    getRange (Proj _ x)            = getRange x
    getRange (Con x)               = getRange x
    getRange (Lit l)               = getRange l
    getRange (QuestionMark i _)    = getRange i
    getRange (Underscore  i)       = getRange i
    getRange (Dot i _)             = getRange i
    getRange (App i _ _)           = getRange i
    getRange (WithApp i _ _)       = getRange i
    getRange (Lam i _ _)           = getRange i
    getRange (AbsurdLam i _)       = getRange i
    getRange (ExtendedLam i _ _ _) = getRange i
    getRange (Pi i _ _)            = getRange i
    getRange (Generalized _ x)     = getRange x
    getRange (Fun i _ _)           = getRange i
    getRange (Set i _)             = getRange i
    getRange (Prop i _)            = getRange i
    getRange (Let i _ _)           = getRange i
    getRange (Rec i _)             = getRange i
    getRange (RecUpdate i _ _)     = getRange i
    getRange (ETel tel)            = getRange tel
    getRange (ScopedExpr _ e)      = getRange e
    getRange (Quote i)             = getRange i
    getRange (QuoteTerm i)         = getRange i
    getRange (Unquote i)           = getRange i
    getRange (Tactic i _ _)        = getRange i
    getRange (DontCare{})          = noRange
    getRange (PatternSyn x)        = getRange x
    getRange (Macro x)             = getRange x

instance HasRange Declaration where
    getRange (Axiom    _ i _ _ _ _  ) = getRange i
    getRange (Generalize _ i _ _ _)   = getRange i
    getRange (Field      i _ _      ) = getRange i
    getRange (Mutual     i _        ) = getRange i
    getRange (Section    i _ _ _    ) = getRange i
    getRange (Apply      i _ _ _ _)   = getRange i
    getRange (Import     i _ _      ) = getRange i
    getRange (Primitive  i _ _      ) = getRange i
    getRange (Pragma     i _        ) = getRange i
    getRange (Open       i _ _      ) = getRange i
    getRange (ScopedDecl _ d        ) = getRange d
    getRange (FunDef     i _ _ _    ) = getRange i
    getRange (DataSig    i _ _ _    ) = getRange i
    getRange (DataDef    i _ _ _ _  ) = getRange i
    getRange (RecSig     i _ _ _    ) = getRange i
    getRange (RecDef i _ _ _ _ _ _ _ _) = getRange i
    getRange (PatternSynDef x _ _   ) = getRange x
    getRange (UnquoteDecl _ i _ _)    = getRange i
    getRange (UnquoteDef i _ _)       = getRange i

instance HasRange (Pattern' e) where
    getRange (VarP x)           = getRange x
    getRange (ConP i _ _)        = getRange i
    getRange (ProjP i _ _)       = getRange i
    getRange (DefP i _ _)        = getRange i
    getRange (WildP i)           = getRange i
    getRange (AsP i _ _)         = getRange i
    getRange (DotP i _)          = getRange i
    getRange (AbsurdP i)         = getRange i
    getRange (LitP l)            = getRange l
    getRange (PatternSynP i _ _) = getRange i
    getRange (RecP i _)          = getRange i
    getRange (EqualP i _)        = getRange i
    getRange (WithP i _)         = getRange i

instance HasRange SpineLHS where
    getRange (SpineLHS i _ _)  = getRange i

instance HasRange LHS where
    getRange (LHS i _)   = getRange i

instance HasRange (LHSCore' e) where
    getRange (LHSHead f ps)         = fuseRange f ps
    getRange (LHSProj d lhscore ps) = d `fuseRange` lhscore `fuseRange` ps
    getRange (LHSWith h wps ps)     = h `fuseRange` wps `fuseRange` ps

instance HasRange a => HasRange (Clause' a) where
    getRange (Clause lhs _ rhs ds catchall) = getRange (lhs, rhs, ds)

instance HasRange RHS where
    getRange AbsurdRHS                 = noRange
    getRange (RHS e _)                 = getRange e
    getRange (WithRHS _ e cs)          = fuseRange e cs
    getRange (RewriteRHS xes _ rhs wh) = getRange (xes, rhs, wh)

instance HasRange WhereDeclarations where
  getRange (WhereDecls _ ds) = getRange ds

instance HasRange LetBinding where
    getRange (LetBind i _ _ _ _     ) = getRange i
    getRange (LetPatBind  i _ _      ) = getRange i
    getRange (LetApply i _ _ _ _     ) = getRange i
    getRange (LetOpen  i _ _         ) = getRange i
    getRange (LetDeclaredVariable x)  = getRange x

-- setRange for patterns applies the range to the outermost pattern constructor
instance SetRange (Pattern' a) where
    setRange r (VarP x)            = VarP (setRange r x)
    setRange r (ConP i ns as)       = ConP (setRange r i) ns as
    setRange r (ProjP _ o ns)       = ProjP (PatRange r) o ns
    setRange r (DefP _ ns as)       = DefP (PatRange r) ns as -- (setRange r n) as
    setRange r (WildP _)            = WildP (PatRange r)
    setRange r (AsP _ n p)          = AsP (PatRange r) (setRange r n) p
    setRange r (DotP _ e)           = DotP (PatRange r) e
    setRange r (AbsurdP _)          = AbsurdP (PatRange r)
    setRange r (LitP l)             = LitP (setRange r l)
    setRange r (PatternSynP _ n as) = PatternSynP (PatRange r) n as
    setRange r (RecP i as)          = RecP (PatRange r) as
    setRange r (EqualP _ es)        = EqualP (PatRange r) es
    setRange r (WithP i p)          = WithP (setRange r i) p

instance KillRange a => KillRange (Binder' a) where
  killRange (Binder a b) = killRange2 Binder a b

instance KillRange LamBinding where
  killRange (DomainFree t x) = killRange2 DomainFree t x
  killRange (DomainFull b)   = killRange1 DomainFull b

instance KillRange GeneralizeTelescope where
  killRange (GeneralizeTel s tel) = GeneralizeTel s (killRange tel)

instance KillRange DataDefParams where
  killRange (DataDefParams s tel) = DataDefParams s (killRange tel)

instance KillRange TypedBinding where
  killRange (TBind r t xs e) = killRange4 TBind r t xs e
  killRange (TLet r lbs)     = killRange2 TLet r lbs

instance KillRange Expr where
  killRange (Var x)                = killRange1 Var x
  killRange (Def x)                = killRange1 Def x
  killRange (Proj o x)             = killRange1 (Proj o) x
  killRange (Con x)                = killRange1 Con x
  killRange (Lit l)                = killRange1 Lit l
  killRange (QuestionMark i ii)    = killRange2 QuestionMark i ii
  killRange (Underscore  i)        = killRange1 Underscore i
  killRange (Dot i e)              = killRange2 Dot i e
  killRange (App i e1 e2)          = killRange3 App i e1 e2
  killRange (WithApp i e es)       = killRange3 WithApp i e es
  killRange (Lam i b e)            = killRange3 Lam i b e
  killRange (AbsurdLam i h)        = killRange2 AbsurdLam i h
  killRange (ExtendedLam i n d ps) = killRange4 ExtendedLam i n d ps
  killRange (Pi i a b)             = killRange3 Pi i a b
  killRange (Generalized s x)      = killRange1 (Generalized s) x
  killRange (Fun i a b)            = killRange3 Fun i a b
  killRange (Set i n)              = killRange2 Set i n
  killRange (Prop i n)             = killRange2 Prop i n
  killRange (Let i ds e)           = killRange3 Let i ds e
  killRange (Rec i fs)             = killRange2 Rec i fs
  killRange (RecUpdate i e fs)     = killRange3 RecUpdate i e fs
  killRange (ETel tel)             = killRange1 ETel tel
  killRange (ScopedExpr s e)       = killRange1 (ScopedExpr s) e
  killRange (Quote i)              = killRange1 Quote i
  killRange (QuoteTerm i)          = killRange1 QuoteTerm i
  killRange (Unquote i)            = killRange1 Unquote i
  killRange (Tactic i e xs)        = killRange3 Tactic i e xs
  killRange (DontCare e)           = killRange1 DontCare e
  killRange (PatternSyn x)         = killRange1 PatternSyn x
  killRange (Macro x)              = killRange1 Macro x

instance KillRange Declaration where
  killRange (Axiom    p i a b c d     ) = killRange4 (\i a c d -> Axiom p i a b c d) i a c d
  killRange (Generalize s i j x e     ) = killRange4 (Generalize s) i j x e
  killRange (Field      i a b         ) = killRange3 Field      i a b
  killRange (Mutual     i a           ) = killRange2 Mutual     i a
  killRange (Section    i a b c       ) = killRange4 Section    i a b c
  killRange (Apply      i a b c d     ) = killRange5 Apply      i a b c d
  killRange (Import     i a b         ) = killRange3 Import     i a b
  killRange (Primitive  i a b         ) = killRange3 Primitive  i a b
  killRange (Pragma     i a           ) = Pragma (killRange i) a
  killRange (Open       i x dir       ) = killRange3 Open       i x dir
  killRange (ScopedDecl a d           ) = killRange1 (ScopedDecl a) d
  killRange (FunDef  i a b c          ) = killRange4 FunDef  i a b c
  killRange (DataSig i a b c          ) = killRange4 DataSig i a b c
  killRange (DataDef i a b c d        ) = killRange5 DataDef i a b c d
  killRange (RecSig  i a b c          ) = killRange4 RecSig  i a b c
  killRange (RecDef  i a b c d e f g h) = killRange9 RecDef  i a b c d e f g h
  killRange (PatternSynDef x xs p     ) = killRange3 PatternSynDef x xs p
  killRange (UnquoteDecl mi i x e     ) = killRange4 UnquoteDecl mi i x e
  killRange (UnquoteDef i x e         ) = killRange3 UnquoteDef i x e

instance KillRange ModuleApplication where
  killRange (SectionApp a b c  ) = killRange3 SectionApp a b c
  killRange (RecordModuleInstance a) = killRange1 RecordModuleInstance a

instance KillRange ScopeCopyInfo where
  killRange (ScopeCopyInfo a b) = killRange2 ScopeCopyInfo a b

instance KillRange e => KillRange (Pattern' e) where
  killRange (VarP x)           = killRange1 VarP x
  killRange (ConP i a b)        = killRange3 ConP i a b
  killRange (ProjP i o a)       = killRange3 ProjP i o a
  killRange (DefP i a b)        = killRange3 DefP i a b
  killRange (WildP i)           = killRange1 WildP i
  killRange (AsP i a b)         = killRange3 AsP i a b
  killRange (DotP i a)          = killRange2 DotP i a
  killRange (AbsurdP i)         = killRange1 AbsurdP i
  killRange (LitP l)            = killRange1 LitP l
  killRange (PatternSynP i a p) = killRange3 PatternSynP i a p
  killRange (RecP i as)         = killRange2 RecP i as
  killRange (EqualP i es)       = killRange2 EqualP i es
  killRange (WithP i p)         = killRange2 WithP i p

instance KillRange SpineLHS where
  killRange (SpineLHS i a b)  = killRange3 SpineLHS i a b

instance KillRange LHS where
  killRange (LHS i a)   = killRange2 LHS i a

instance KillRange e => KillRange (LHSCore' e) where
  killRange (LHSHead a b)   = killRange2 LHSHead a b
  killRange (LHSProj a b c) = killRange3 LHSProj a b c
  killRange (LHSWith a b c) = killRange3 LHSWith a b c

instance KillRange a => KillRange (Clause' a) where
  killRange (Clause lhs spats rhs ds catchall) = killRange5 Clause lhs spats rhs ds catchall

instance KillRange ProblemEq where
  killRange (ProblemEq p v a) = killRange3 ProblemEq p v a

instance KillRange RHS where
  killRange AbsurdRHS                = AbsurdRHS
  killRange (RHS e c)                = killRange2 RHS e c
  killRange (WithRHS q e cs)         = killRange3 WithRHS q e cs
  killRange (RewriteRHS xes spats rhs wh) = killRange4 RewriteRHS xes spats rhs wh

instance KillRange WhereDeclarations where
  killRange (WhereDecls a b) = killRange2 WhereDecls a b

instance KillRange LetBinding where
  killRange (LetBind   i info a b c) = killRange5 LetBind i info a b c
  killRange (LetPatBind i a b       ) = killRange3 LetPatBind i a b
  killRange (LetApply   i a b c d   ) = killRange5 LetApply i a b c d
  killRange (LetOpen    i x dir     ) = killRange3 LetOpen  i x dir
  killRange (LetDeclaredVariable x)  = killRange1 LetDeclaredVariable x

-- See Agda.Utils.GeniPlate:
-- Does not descend into ScopeInfo and renaming maps, for instance.

instanceUniverseBiT' [] [t| (Declaration, QName)          |]
instanceUniverseBiT' [] [t| (Declaration, AmbiguousQName) |]
instanceUniverseBiT' [] [t| (Declaration, Expr)           |]
instanceUniverseBiT' [] [t| (Declaration, LetBinding)     |]
instanceUniverseBiT' [] [t| (Declaration, LamBinding)     |]
instanceUniverseBiT' [] [t| (Declaration, TypedBinding)   |]
instanceUniverseBiT' [] [t| (Declaration, Pattern)        |]
instanceUniverseBiT' [] [t| (Declaration, Pattern' Void)  |]
instanceUniverseBiT' [] [t| (Declaration, Declaration)    |]
instanceUniverseBiT' [] [t| (Declaration, ModuleName)     |]
instanceUniverseBiT' [] [t| (Declaration, ModuleInfo)     |]
instanceUniverseBiT' [] [t| (Declaration, NamedArg LHSCore)  |]
instanceUniverseBiT' [] [t| (Declaration, NamedArg BindName) |]
instanceUniverseBiT' [] [t| (Declaration, NamedArg Expr)     |]
instanceUniverseBiT' [] [t| (Declaration, NamedArg Pattern)  |]
instanceUniverseBiT' [] [t| (Declaration, Quantity)          |]

------------------------------------------------------------------------
-- Queries
------------------------------------------------------------------------

-- | Extracts all the names which are declared in a 'Declaration'.
-- This does not include open public or let expressions, but it does
-- include local modules, where clauses and the names of extended
-- lambdas.

class AllNames a where
  allNames :: a -> Seq QName

instance AllNames a => AllNames [a] where
  allNames = Fold.foldMap allNames

instance AllNames a => AllNames (Maybe a) where
  allNames = Fold.foldMap allNames

instance AllNames a => AllNames (Arg a) where
  allNames = Fold.foldMap allNames

instance AllNames a => AllNames (Named name a) where
  allNames = Fold.foldMap allNames

instance (AllNames a, AllNames b) => AllNames (a,b) where
  allNames (a,b) = allNames a >< allNames b

instance (AllNames a, AllNames b, AllNames c) => AllNames (a,b,c) where
  allNames (a,b,c) = allNames a >< allNames b >< allNames c

instance AllNames QName where
  allNames q = Seq.singleton q

instance AllNames Declaration where
  allNames (Axiom   _ _ _ _ q _)      = Seq.singleton q
  allNames (Generalize _ _ _ q _)     = Seq.singleton q
  allNames (Field     _   q _)        = Seq.singleton q
  allNames (Primitive _   q _)        = Seq.singleton q
  allNames (Mutual     _ defs)        = allNames defs
  allNames (DataSig _ q _ _)          = Seq.singleton q
  allNames (DataDef _ q _ _ decls)    = q <| allNames decls
  allNames (RecSig _ q _ _)           = Seq.singleton q
  allNames (RecDef _ q _ _ _ c _ _ decls) = q <| allNames c >< allNames decls
  allNames (PatternSynDef q _ _)      = Seq.singleton q
  allNames (UnquoteDecl _ _ qs _)     = Seq.fromList qs
  allNames (UnquoteDef _ qs _)        = Seq.fromList qs
  allNames (FunDef _ q _ cls)         = q <| allNames cls
  allNames (Section _ _ _ decls)      = allNames decls
  allNames Apply{}                    = Seq.empty
  allNames Import{}                   = Seq.empty
  allNames Pragma{}                   = Seq.empty
  allNames Open{}                     = Seq.empty
  allNames (ScopedDecl _ decls)       = allNames decls

instance AllNames Clause where
  allNames cl = allNames (clauseRHS cl, clauseWhereDecls cl)

instance (AllNames qn, AllNames e) => AllNames (RewriteEqn' qn p e) where
    allNames = \case
      Rewrite es    -> Fold.foldMap allNames es
      Invert qn pes -> allNames qn >< foldMap (Fold.foldMap allNames) pes

instance AllNames RHS where
  allNames (RHS e _)                 = allNames e
  allNames AbsurdRHS{}               = Seq.empty
  allNames (WithRHS q _ cls)         = q <| allNames cls
  allNames (RewriteRHS qes _ rhs cls) = allNames (qes, rhs, cls)

instance AllNames WhereDeclarations where
  allNames (WhereDecls _ ds) = allNames ds

instance AllNames Expr where
  allNames Var{}                   = Seq.empty
  allNames Def{}                   = Seq.empty
  allNames Proj{}                  = Seq.empty
  allNames Con{}                   = Seq.empty
  allNames Lit{}                   = Seq.empty
  allNames QuestionMark{}          = Seq.empty
  allNames Underscore{}            = Seq.empty
  allNames (Dot _ e)               = allNames e
  allNames (App _ e1 e2)           = allNames e1 >< allNames e2
  allNames (WithApp _ e es)        = allNames e >< allNames es
  allNames (Lam _ b e)             = allNames b >< allNames e
  allNames AbsurdLam{}             = Seq.empty
  allNames (ExtendedLam _ _ q cls) = q <| allNames cls
  allNames (Pi _ tel e)            = allNames tel >< allNames e
  allNames (Generalized s e)       = Seq.fromList (Set.toList s) >< allNames e  -- TODO: or just (allNames e)?
  allNames (Fun _ e1 e2)           = allNames e1 >< allNames e2
  allNames Set{}                   = Seq.empty
  allNames Prop{}                  = Seq.empty
  allNames (Let _ lbs e)           = allNames lbs >< allNames e
  allNames ETel{}                  = __IMPOSSIBLE__
  allNames (Rec _ fields)          = allNames [ a ^. exprFieldA | Left a <- fields ]
  allNames (RecUpdate _ e fs)      = allNames e >< allNames (map (view exprFieldA) fs)
  allNames (ScopedExpr _ e)        = allNames e
  allNames Quote{}                 = Seq.empty
  allNames QuoteTerm{}             = Seq.empty
  allNames Unquote{}               = Seq.empty
  allNames (Tactic _ e xs)         = allNames e >< allNames xs
  allNames DontCare{}              = Seq.empty
  allNames PatternSyn{}            = Seq.empty
  allNames Macro{}                 = Seq.empty

instance AllNames LamBinding where
  allNames DomainFree{}       = Seq.empty
  allNames (DomainFull binds) = allNames binds

instance AllNames TypedBinding where
  allNames (TBind _ t _ e) = allNames (t, e)
  allNames (TLet _ lbs)  = allNames lbs

instance AllNames LetBinding where
  allNames (LetBind _ _ _ e1 e2)  = allNames e1 >< allNames e2
  allNames (LetPatBind _ _ e)      = allNames e
  allNames (LetApply _ _ app _ _)  = allNames app
  allNames LetOpen{}               = Seq.empty
  allNames (LetDeclaredVariable _) = Seq.empty

instance AllNames ModuleApplication where
  allNames (SectionApp bindss _ es) = allNames bindss >< allNames es
  allNames RecordModuleInstance{}   = Seq.empty

-- | The name defined by the given axiom.
--
-- Precondition: The declaration has to be a (scoped) 'Axiom'.

axiomName :: Declaration -> QName
axiomName (Axiom _ _ _ _ q _)  = q
axiomName (ScopedDecl _ (d:_)) = axiomName d
axiomName _                    = __IMPOSSIBLE__

-- | Are we in an abstract block?
--
--   In that case some definition is abstract.
class AnyAbstract a where
  anyAbstract :: a -> Bool

instance AnyAbstract a => AnyAbstract [a] where
  anyAbstract = Fold.any anyAbstract

instance AnyAbstract Declaration where
  anyAbstract (Axiom _ i _ _ _ _)    = defAbstract i == AbstractDef
  anyAbstract (Field i _ _)          = defAbstract i == AbstractDef
  anyAbstract (Mutual     _ ds)      = anyAbstract ds
  anyAbstract (ScopedDecl _ ds)      = anyAbstract ds
  anyAbstract (Section _ _ _ ds)     = anyAbstract ds
  anyAbstract (FunDef i _ _ _)       = defAbstract i == AbstractDef
  anyAbstract (DataDef i _ _ _ _)    = defAbstract i == AbstractDef
  anyAbstract (RecDef i _ _ _ _ _ _ _ _) = defAbstract i == AbstractDef
  anyAbstract (DataSig i _ _ _)      = defAbstract i == AbstractDef
  anyAbstract (RecSig i _ _ _)       = defAbstract i == AbstractDef
  anyAbstract _                      = __IMPOSSIBLE__

-- | Turn a name into an expression.

class NameToExpr a where
  nameToExpr :: a -> Expr

-- | Turn an 'AbstractName' into an expression.

instance NameToExpr AbstractName where
  nameToExpr d =
    case anameKind d of
      DataName                 -> Def x
      RecName                  -> Def x
      AxiomName                -> Def x
      PrimName                 -> Def x
      FunName                  -> Def x
      OtherDefName             -> Def x
      GeneralizeName           -> Def x
      DisallowedGeneralizeName -> Def x
      FldName                  -> Proj ProjSystem ux
      ConName                  -> Con ux
      PatternSynName           -> PatternSyn ux
      MacroName                -> Macro x
      QuotableName             -> App (defaultAppInfo r) (Quote i) (defaultNamedArg $ Def x)
    where
    x  = anameName d
    ux = unambiguous x
    r  = getRange x
    i  = ExprRange r

-- | Turn a 'ResolvedName' into an expression.
--
--   Assumes name is not 'UnknownName'.

instance NameToExpr ResolvedName where
  nameToExpr = \case
    VarName x _          -> Var x
    DefinedName _ x      -> nameToExpr x  -- Can be 'isDefName', 'MacroName', 'QuotableName'.
    FieldName xs         -> Proj ProjSystem . AmbQ . fmap anameName $ xs
    ConstructorName xs   -> Con . AmbQ . fmap anameName $ xs
    PatternSynResName xs -> PatternSyn . AmbQ . fmap anameName $ xs
    UnknownName          -> __IMPOSSIBLE__

app :: Expr -> [NamedArg Expr] -> Expr
app = foldl (App defaultAppInfo_)

mkLet :: ExprInfo -> [LetBinding] -> Expr -> Expr
mkLet i [] e = e
mkLet i ds e = Let i ds e

patternToExpr :: Pattern -> Expr
patternToExpr = \case
  VarP x             -> Var (unBind x)
  ConP _ c ps        -> Con c `app` map (fmap (fmap patternToExpr)) ps
  ProjP _ o ds       -> Proj o ds
  DefP _ fs ps       -> Def (headAmbQ fs) `app` map (fmap (fmap patternToExpr)) ps
  WildP _            -> Underscore emptyMetaInfo
  AsP _ _ p          -> patternToExpr p
  DotP _ e           -> e
  AbsurdP _          -> Underscore emptyMetaInfo  -- TODO: could this happen?
  LitP l             -> Lit l
  PatternSynP _ c ps -> PatternSyn c `app` (map . fmap . fmap) patternToExpr ps
  RecP _ as          -> Rec exprNoRange $ map (Left . fmap patternToExpr) as
  EqualP{}           -> __IMPOSSIBLE__  -- Andrea TODO: where is this used?
  WithP r p          -> __IMPOSSIBLE__

type PatternSynDefn = ([Arg Name], Pattern' Void)
type PatternSynDefns = Map QName PatternSynDefn

lambdaLiftExpr :: [Name] -> Expr -> Expr
lambdaLiftExpr []     e = e
lambdaLiftExpr (n:ns) e =
  Lam exprNoRange (mkDomainFree $ defaultNamedArg $ mkBinder_ n) $
  lambdaLiftExpr ns e

class SubstExpr a where
  substExpr :: [(Name, Expr)] -> a -> a

instance SubstExpr a => SubstExpr (Maybe a) where
  substExpr = fmap . substExpr

instance SubstExpr a => SubstExpr [a] where
  substExpr = fmap . substExpr

instance SubstExpr a => SubstExpr (Arg a) where
  substExpr = fmap . substExpr

instance SubstExpr a => SubstExpr (Named name a) where
  substExpr = fmap . substExpr

instance (SubstExpr a, SubstExpr b) => SubstExpr (a, b) where
  substExpr s (x, y) = (substExpr s x, substExpr s y)

instance (SubstExpr a, SubstExpr b) => SubstExpr (Either a b) where
  substExpr s (Left x)  = Left (substExpr s x)
  substExpr s (Right y) = Right (substExpr s y)

instance SubstExpr C.Name where
  substExpr _ = id

instance SubstExpr ModuleName where
  substExpr _ = id

instance SubstExpr Assign where
  substExpr s (FieldAssignment n x) = FieldAssignment n (substExpr s x)

instance SubstExpr Expr where
  substExpr s e = case e of
    Var n                 -> fromMaybe e (lookup n s)
    Def _                 -> e
    Proj{}                -> e
    Con _                 -> e
    Lit _                 -> e
    QuestionMark{}        -> e
    Underscore   _        -> e
    Dot i e               -> Dot i (substExpr s e)
    App  i e e'           -> App i (substExpr s e) (substExpr s e')
    WithApp i e es        -> WithApp i (substExpr s e) (substExpr s es)
    Lam  i lb e           -> Lam i lb (substExpr s e)
    AbsurdLam i h         -> e
    ExtendedLam i di n cs -> __IMPOSSIBLE__   -- Maybe later...
    Pi   i t e            -> Pi i (substExpr s t) (substExpr s e)
    Generalized ns e      -> Generalized ns (substExpr s e)
    Fun  i ae e           -> Fun i (substExpr s ae) (substExpr s e)
    Set  i n              -> e
    Prop i n              -> e
    Let  i ls e           -> Let i (substExpr s ls) (substExpr s e)
    ETel t                -> e
    Rec  i nes            -> Rec i (substExpr s nes)
    RecUpdate i e nes     -> RecUpdate i (substExpr s e) (substExpr s nes)
    -- XXX: Do we need to do more with ScopedExprs?
    ScopedExpr si e       -> ScopedExpr si (substExpr s e)
    Quote i               -> e
    QuoteTerm i           -> e
    Unquote i             -> e
    Tactic i e xs         -> Tactic i (substExpr s e) (substExpr s xs)
    DontCare e            -> DontCare (substExpr s e)
    PatternSyn{}          -> e
    Macro{}               -> e

instance SubstExpr LetBinding where
  substExpr s lb = case lb of
    LetBind i r n e e' -> LetBind i r n (substExpr s e) (substExpr s e')
    LetPatBind i p e   -> LetPatBind i p (substExpr s e) -- Andreas, 2012-06-04: what about the pattern p
    _                  -> lb -- Nicolas, 2013-11-11: what about "LetApply" there is experessions in there

instance SubstExpr TypedBinding where
  substExpr s tb = case tb of
    TBind r t ns e -> TBind r (substExpr s t) ns $ substExpr s e
    TLet r lbs     -> TLet r $ substExpr s lbs

-- TODO: more informative failure
insertImplicitPatSynArgs
  :: HasRange a
  => (Range -> a)
  -> Range
  -> [Arg Name]
  -> [NamedArg a]
  -> Maybe ([(Name, a)], [Arg Name])
insertImplicitPatSynArgs wild r ns as = matchArgs r ns as
  where
    matchNextArg r n as@(~(a : as'))
      | matchNext n as = return (namedArg a, as')
      | visible n      = Nothing
      | otherwise      = return (wild r, as)

    matchNext _ [] = False
    matchNext n (a:as) = sameHiding n a && maybe True (x ==) (bareNameOf a)
      where
        x = C.nameToRawName $ nameConcrete $ unArg n

    matchArgs r [] []     = return ([], [])
    matchArgs r [] as     = Nothing
    matchArgs r (n:ns) [] | visible n = return ([], n : ns)    -- under-applied
    matchArgs r (n:ns) as = do
      (p, as) <- matchNextArg r n as
      first ((unArg n, p) :) <$> matchArgs (getRange p) ns as
