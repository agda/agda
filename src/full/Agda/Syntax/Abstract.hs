
{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Agda.Syntax.Internal").
-}
module Agda.Syntax.Abstract
    ( module Agda.Syntax.Abstract
    , module Agda.Syntax.Abstract.Name
    ) where

import Prelude hiding (null)

import Control.DeepSeq

import Data.Bifunctor
import qualified Data.Foldable as Fold
import Data.Function (on)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Sequence (Seq, (<|), (><))
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Void
import Data.Data (Data)

import GHC.Generics (Generic)

import Agda.Syntax.Concrete (FieldAssignment'(..), exprFieldA)--, HoleContent'(..))
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Positivity.Occurrence

import Agda.Utils.Lens
import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Null
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
  deriving (Show, Data, HasRange, KillRange, SetRange, NFData)

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

-- | Types are just expressions.
-- Use this type synonym for hinting that an expression should be a type.
type Type = Expr

-- | Expressions after scope checking (operators parsed, names resolved).
data Expr
  = Var  Name                          -- ^ Bound variable.
  | Def'  QName Suffix                 -- ^ Constant: axiom, function, data or record type,
                                       --   with a possible suffix.
  | Proj ProjOrigin AmbiguousQName     -- ^ Projection (overloaded).
  | Con  AmbiguousQName                -- ^ Constructor (overloaded).
  | PatternSyn AmbiguousQName          -- ^ Pattern synonym.
  | Macro QName                        -- ^ Macro.
  | Lit ExprInfo Literal               -- ^ Literal.
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
  | ExtendedLam ExprInfo DefInfo Erased QName (List1 Clause)
  | Pi   ExprInfo Telescope1 Type      -- ^ Dependent function space @Γ → A@.
  | Generalized (Set QName) Type       -- ^ Like a Pi, but the ordering is not known
  | Fun  ExprInfo (Arg Type) Type      -- ^ Non-dependent function space.
  | Let  ExprInfo (List1 LetBinding) Expr
                                       -- ^ @let bs in e@.
  | ETel Telescope                     -- ^ Only used when printing telescopes.
  | Rec  ExprInfo RecordAssigns        -- ^ Record construction.
  | RecUpdate ExprInfo Expr Assigns    -- ^ Record update.
  | ScopedExpr ScopeInfo Expr          -- ^ Scope annotation.
  | Quote ExprInfo                     -- ^ Quote an identifier 'QName'.
  | QuoteTerm ExprInfo                 -- ^ Quote a term.
  | Unquote ExprInfo                   -- ^ The splicing construct: unquote ...
  | DontCare Expr                      -- ^ For printing @DontCare@ from @Syntax.Internal@.
  deriving (Data, Show, Generic)

-- | Pattern synonym for regular 'Def'.
pattern Def :: QName -> Expr
pattern Def x = Def' x NoSuffix

-- | Smart constructor for 'Generalized'.
generalized :: Set QName -> Type -> Type
generalized s e
    | null s    = e
    | otherwise = Generalized s e

-- | Record field assignment @f = e@.
type Assign  = FieldAssignment' Expr
type Assigns = [Assign]
type RecordAssign  = Either Assign ModuleName
type RecordAssigns = [RecordAssign]

-- | Renaming (generic).
type Ren a = Map a (List1 a)

data ScopeCopyInfo = ScopeCopyInfo
  { renModules :: Ren ModuleName
  , renNames   :: Ren QName }
  deriving (Eq, Show, Data, Generic)

initCopyInfo :: ScopeCopyInfo
initCopyInfo = ScopeCopyInfo
  { renModules = mempty
  , renNames   = mempty
  }

instance Pretty ScopeCopyInfo where
  pretty i = vcat [ prRen "renModules =" (renModules i)
                  , prRen "renNames   =" (renNames i) ]
    where
      prRen s r = sep [ text s, nest 2 $ vcat (map pr xs) ]
        where
          xs = [ (k, v) | (k, vs) <- Map.toList r, v <- List1.toList vs ]
      pr (x, y) = pretty x <+> "->" <+> pretty y

type RecordDirectives = RecordDirectives' QName

data Declaration
  = Axiom      KindOfName DefInfo ArgInfo (Maybe [Occurrence]) QName Type
    -- ^ Type signature (can be irrelevant, but not hidden).
    --
    -- The fourth argument contains an optional assignment of
    -- polarities to arguments.
  | Generalize (Set QName) DefInfo ArgInfo QName Type
    -- ^ First argument is set of generalizable variables used in the type.
  | Field      DefInfo QName (Arg Type)              -- ^ record field
  | Primitive  DefInfo QName (Arg Type)              -- ^ primitive function
  | Mutual     MutualInfo [Declaration]              -- ^ a bunch of mutually recursive definitions
  | Section    Range ModuleName GeneralizeTelescope [Declaration]
  | Apply      ModuleInfo ModuleName ModuleApplication ScopeCopyInfo ImportDirective
    -- ^ The @ImportDirective@ is for highlighting purposes.
  | Import     ModuleInfo ModuleName ImportDirective
    -- ^ The @ImportDirective@ is for highlighting purposes.
  | Pragma     Range      Pragma
  | Open       ModuleInfo ModuleName ImportDirective
    -- ^ only retained for highlighting purposes
  | FunDef     DefInfo QName Delayed [Clause] -- ^ sequence of function clauses
  | DataSig    DefInfo QName GeneralizeTelescope Type -- ^ lone data signature
  | DataDef    DefInfo QName UniverseCheck DataDefParams [Constructor]
  | RecSig     DefInfo QName GeneralizeTelescope Type -- ^ lone record signature
  | RecDef     DefInfo QName UniverseCheck RecordDirectives DataDefParams Type [Declaration]
      -- ^ The 'Type' gives the constructor type telescope, @(x1 : A1)..(xn : An) -> Prop@,
      --   and the optional name is the constructor's name.
      --   The optional 'Range' is for the @pattern@ attribute.
  | PatternSynDef QName [Arg BindName] (Pattern' Void)
      -- ^ Only for highlighting purposes
  | UnquoteDecl MutualInfo [DefInfo] [QName] Expr
  | UnquoteDef  [DefInfo] [QName] Expr
  | ScopedDecl ScopeInfo [Declaration]  -- ^ scope annotation
  deriving (Data, Show, Generic)

type DefInfo = DefInfo' Expr

type ImportDirective = ImportDirective' QName ModuleName
type Renaming        = Renaming'        QName ModuleName
type ImportedName    = ImportedName'    QName ModuleName

data ModuleApplication
    = SectionApp Telescope ModuleName [NamedArg Expr]
      -- ^ @tel. M args@:  applies @M@ to @args@ and abstracts @tel@.
    | RecordModuleInstance ModuleName
      -- ^ @M {{...}}@
  deriving (Data, Show, Eq, Generic)

data Pragma
  = OptionsPragma [String]
  | BuiltinPragma RString ResolvedName
    -- ^ 'ResolvedName' is not 'UnknownName'.
    --   Name can be ambiguous e.g. for built-in constructors.
  | BuiltinNoDefPragma RString KindOfName QName
    -- ^ Builtins that do not come with a definition,
    --   but declare a name for an Agda concept.
  | RewritePragma Range [QName]
    -- ^ Range is range of REWRITE keyword.
  | CompilePragma RString QName String
  | StaticPragma QName
  | EtaPragma QName
    -- ^ For coinductive records, use pragma instead of regular
    --   @eta-equality@ definition (as it is might make Agda loop).
  | InjectivePragma QName
  | InlinePragma Bool QName -- INLINE or NOINLINE
  | DisplayPragma QName [NamedArg Pattern] Expr
  deriving (Data, Show, Eq, Generic)

-- | Bindings that are valid in a @let@.
data LetBinding
  = LetBind LetInfo ArgInfo BindName Type Expr
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
  deriving (Data, Show, Eq, Generic)

-- | Only 'Axiom's.
type TypeSignature  = Declaration
type Constructor    = TypeSignature
type Field          = TypeSignature

type TacticAttr = Maybe Expr

-- A Binder @x\@p@, the pattern is optional
data Binder' a = Binder
  { binderPattern :: Maybe Pattern
  , binderName    :: a
  } deriving (Data, Show, Eq, Functor, Foldable, Traversable, Generic)

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
  deriving (Data, Show, Eq, Generic)

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
  = TBind Range TacticAttr (List1 (NamedArg Binder)) Type
    -- ^ As in telescope @(x y z : A)@ or type @(x y z : A) -> B@.
  | TLet Range (List1 LetBinding)
    -- ^ E.g. @(let x = e)@ or @(let open M)@.
  deriving (Data, Show, Eq, Generic)

mkTBind :: Range -> List1 (NamedArg Binder) -> Type -> TypedBinding
mkTBind r = TBind r Nothing

mkTLet :: Range -> [LetBinding] -> Maybe TypedBinding
mkTLet _ []     = Nothing
mkTLet r (d:ds) = Just $ TLet r (d :| ds)

type Telescope1 = List1 TypedBinding
type Telescope  = [TypedBinding]

mkPi :: ExprInfo -> Telescope -> Type -> Type
mkPi i []     e = e
mkPi i (x:xs) e = Pi i (x :| xs) e

data GeneralizeTelescope = GeneralizeTel
  { generalizeTelVars :: Map QName Name
    -- ^ Maps generalize variables to the corresponding bound variable (to be
    --   introduced by the generalisation).
  , generalizeTel     :: Telescope }
  deriving (Data, Show, Eq, Generic)

data DataDefParams = DataDefParams
  { dataDefGeneralizedParams :: Set Name
    -- ^ We don't yet know the position of generalized parameters from the data
    --   sig, so we keep these in a set on the side.
  , dataDefParams :: [LamBinding]
  }
  deriving (Data, Show, Eq, Generic)

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
--    * User pattern is an annotated wildcard:
--      type annotation will be checked after splitting is complete.
data ProblemEq = ProblemEq
  { problemInPat :: Pattern
  , problemInst  :: I.Term
  , problemType  :: I.Dom I.Type
  } deriving (Data, Show, Generic)

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
  } deriving (Data, Show, Functor, Foldable, Traversable, Eq, Generic)

data WhereDeclarations = WhereDecls
  { whereModule :: Maybe ModuleName
      -- #2897: we need to restrict named where modules in refined contexts,
      --        so remember whether it was named here
  , whereAnywhere :: Bool
      -- ^ is it an ordinary unnamed @where@?
  , whereDecls :: Maybe Declaration
      -- ^ The declaration is a 'Section'.
  } deriving (Data, Show, Eq, Generic)

instance Null WhereDeclarations where
  empty = WhereDecls empty False empty

noWhereDecls :: WhereDeclarations
noWhereDecls = empty

type Clause = Clause' LHS
type SpineClause = Clause' SpineLHS
type RewriteEqn  = RewriteEqn' QName BindName Pattern Expr
type WithExpr' e = Named BindName (Arg e)
type WithExpr    = WithExpr' Expr

data RHS
  = RHS
    { rhsExpr     :: Expr
    , rhsConcrete :: Maybe C.Expr
      -- ^ We store the original concrete expression in case
      --   we have to reproduce it during interactive case splitting.
      --   'Nothing' for internally generated rhss.
    }
  | AbsurdRHS
  | WithRHS QName [WithExpr] [Clause]
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
  deriving (Data, Show, Generic)

-- | Ignore 'rhsConcrete' when comparing 'RHS's.
instance Eq RHS where
  RHS e _          == RHS e' _            = e == e'
  AbsurdRHS        == AbsurdRHS           = True
  WithRHS a b c    == WithRHS a' b' c'    = (a == a') && (b == b') && (c == c')
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
  deriving (Data, Show, Eq, Generic)

-- | Ignore 'Range' when comparing 'LHS's.
instance Eq LHS where
  LHS _ core == LHS _ core' = core == core'

-- | The lhs of a clause in focused (projection-application) view (outside-in).
--   Projection patters are represented as 'LHSProj's.
data LHS = LHS
  { lhsInfo     :: LHSInfo               -- ^ Range.
  , lhsCore     :: LHSCore               -- ^ Copatterns.
  }
  deriving (Data, Show, Generic)

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
             , lhsWithPatterns :: [Arg (Pattern' e)]
                 -- ^ Applied to with patterns @| p1 | ... | pn@.
                 --   These patterns are not prefixed with @WithP@!
             , lhsPats         :: [NamedArg (Pattern' e)]
                 -- ^ Further applied to patterns.
             }
  deriving (Data, Show, Functor, Foldable, Traversable, Eq, Generic)

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
  | LitP PatInfo Literal
  | PatternSynP PatInfo AmbiguousQName (NAPs e)
  | RecP PatInfo [FieldAssignment' (Pattern' e)]
  | EqualP PatInfo [(e, e)]
  | WithP PatInfo (Pattern' e)  -- ^ @| p@, for with-patterns.
  | AnnP PatInfo e (Pattern' e) -- ^ Pattern with type annotation
  deriving (Data, Show, Functor, Foldable, Traversable, Eq, Generic)

type NAPs e   = [NamedArg (Pattern' e)]
type NAPs1 e  = List1 (NamedArg (Pattern' e))
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

type HoleContent = C.HoleContent' () BindName Pattern Expr

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

-- | Does not compare 'ScopeInfo' fields.
--   Does not distinguish between prefix and postfix projections.

instance Eq Expr where
  ScopedExpr _ a1            == ScopedExpr _ a2            = a1 == a2

  Var a1                     == Var a2                     = a1 == a2
  Def' a1 s1                 == Def' a2 s2                 = (a1, s1) == (a2, s2)
  Proj _ a1                  == Proj _ a2                  = a1 == a2
  Con a1                     == Con a2                     = a1 == a2
  PatternSyn a1              == PatternSyn a2              = a1 == a2
  Macro a1                   == Macro a2                   = a1 == a2
  Lit r1 a1                  == Lit r2 a2                  = (r1, a1) == (r2, a2)
  QuestionMark a1 b1         == QuestionMark a2 b2         = (a1, b1) == (a2, b2)
  Underscore a1              == Underscore a2              = a1 == a2
  Dot r1 e1                  == Dot r2 e2                  = (r1, e1) == (r2, e2)
  App a1 b1 c1               == App a2 b2 c2               = (a1, b1, c1) == (a2, b2, c2)
  WithApp a1 b1 c1           == WithApp a2 b2 c2           = (a1, b1, c1) == (a2, b2, c2)
  Lam a1 b1 c1               == Lam a2 b2 c2               = (a1, b1, c1) == (a2, b2, c2)
  AbsurdLam a1 b1            == AbsurdLam a2 b2            = (a1, b1) == (a2, b2)
  ExtendedLam a1 b1 c1 d1 e1 == ExtendedLam a2 b2 c2 d2 e2 = (a1, b1, c1, d1, e1) ==
                                                             (a2, b2, c2, d2, e2)
  Pi a1 b1 c1                == Pi a2 b2 c2                = (a1, b1, c1) == (a2, b2, c2)
  Generalized a1 b1          == Generalized a2 b2          = (a1, b1) == (a2, b2)
  Fun a1 b1 c1               == Fun a2 b2 c2               = (a1, b1, c1) == (a2, b2, c2)
  Let a1 b1 c1               == Let a2 b2 c2               = (a1, b1, c1) == (a2, b2, c2)
  ETel a1                    == ETel a2                    = a1 == a2
  Rec a1 b1                  == Rec a2 b2                  = (a1, b1) == (a2, b2)
  RecUpdate a1 b1 c1         == RecUpdate a2 b2 c2         = (a1, b1, c1) == (a2, b2, c2)
  Quote a1                   == Quote a2                   = a1 == a2
  QuoteTerm a1               == QuoteTerm a2               = a1 == a2
  Unquote a1                 == Unquote a2                 = a1 == a2
  DontCare a1                == DontCare a2                = a1 == a2

  _                          == _                          = False

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
  RecDef a1 b1 c1 d1 e1 f1 g1    == RecDef a2 b2 c2 d2 e2 f2 g2    = (a1, b1, c1, d1, e1, f1, g1) == (a2, b2, c2, d2, e2, f2, g2)
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
  getHiding (TBind _ _ (x :|_) _) = getHiding x   -- Slightly dubious
  getHiding TLet{}                = mempty
  mapHiding f (TBind r t xs e)    = TBind r t ((fmap . mapHiding) f xs) e
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
    getRange (Var x)                 = getRange x
    getRange (Def' x _)              = getRange x
    getRange (Proj _ x)              = getRange x
    getRange (Con x)                 = getRange x
    getRange (Lit i _)               = getRange i
    getRange (QuestionMark i _)      = getRange i
    getRange (Underscore  i)         = getRange i
    getRange (Dot i _)               = getRange i
    getRange (App i _ _)             = getRange i
    getRange (WithApp i _ _)         = getRange i
    getRange (Lam i _ _)             = getRange i
    getRange (AbsurdLam i _)         = getRange i
    getRange (ExtendedLam i _ _ _ _) = getRange i
    getRange (Pi i _ _)              = getRange i
    getRange (Generalized _ x)       = getRange x
    getRange (Fun i _ _)             = getRange i
    getRange (Let i _ _)             = getRange i
    getRange (Rec i _)               = getRange i
    getRange (RecUpdate i _ _)       = getRange i
    getRange (ETel tel)              = getRange tel
    getRange (ScopedExpr _ e)        = getRange e
    getRange (Quote i)               = getRange i
    getRange (QuoteTerm i)           = getRange i
    getRange (Unquote i)             = getRange i
    getRange (DontCare{})            = noRange
    getRange (PatternSyn x)          = getRange x
    getRange (Macro x)               = getRange x

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
    getRange (RecDef i _ _ _ _ _ _)   = getRange i
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
    getRange (LitP i l)          = getRange i
    getRange (PatternSynP i _ _) = getRange i
    getRange (RecP i _)          = getRange i
    getRange (EqualP i _)        = getRange i
    getRange (WithP i _)         = getRange i
    getRange (AnnP i _ _)        = getRange i

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
  getRange (WhereDecls _ _ ds) = getRange ds

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
    setRange r (LitP _ l)           = LitP (PatRange r) l
    setRange r (PatternSynP _ n as) = PatternSynP (PatRange r) n as
    setRange r (RecP i as)          = RecP (PatRange r) as
    setRange r (EqualP _ es)        = EqualP (PatRange r) es
    setRange r (WithP i p)          = WithP (setRange r i) p
    setRange r (AnnP i a p)         = AnnP (setRange r i) a p

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
  killRange (Var x)                  = killRange1 Var x
  killRange (Def' x v)               = killRange2 Def' x v
  killRange (Proj o x)               = killRange1 (Proj o) x
  killRange (Con x)                  = killRange1 Con x
  killRange (Lit i l)                = killRange2 Lit i l
  killRange (QuestionMark i ii)      = killRange2 QuestionMark i ii
  killRange (Underscore  i)          = killRange1 Underscore i
  killRange (Dot i e)                = killRange2 Dot i e
  killRange (App i e1 e2)            = killRange3 App i e1 e2
  killRange (WithApp i e es)         = killRange3 WithApp i e es
  killRange (Lam i b e)              = killRange3 Lam i b e
  killRange (AbsurdLam i h)          = killRange2 AbsurdLam i h
  killRange (ExtendedLam i n e d ps) = killRange5 ExtendedLam i n e d ps
  killRange (Pi i a b)               = killRange3 Pi i a b
  killRange (Generalized s x)        = killRange1 (Generalized s) x
  killRange (Fun i a b)              = killRange3 Fun i a b
  killRange (Let i ds e)             = killRange3 Let i ds e
  killRange (Rec i fs)               = killRange2 Rec i fs
  killRange (RecUpdate i e fs)       = killRange3 RecUpdate i e fs
  killRange (ETel tel)               = killRange1 ETel tel
  killRange (ScopedExpr s e)         = killRange1 (ScopedExpr s) e
  killRange (Quote i)                = killRange1 Quote i
  killRange (QuoteTerm i)            = killRange1 QuoteTerm i
  killRange (Unquote i)              = killRange1 Unquote i
  killRange (DontCare e)             = killRange1 DontCare e
  killRange (PatternSyn x)           = killRange1 PatternSyn x
  killRange (Macro x)                = killRange1 Macro x

instance KillRange Suffix where
  killRange = id

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
  killRange (RecDef  i a b c d e f    ) = killRange7 RecDef  i a b c d e f
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
  killRange (LitP i l)          = killRange2 LitP i l
  killRange (PatternSynP i a p) = killRange3 PatternSynP i a p
  killRange (RecP i as)         = killRange2 RecP i as
  killRange (EqualP i es)       = killRange2 EqualP i es
  killRange (WithP i p)         = killRange2 WithP i p
  killRange (AnnP i a p)        = killRange3 AnnP i a p

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
  killRange (WhereDecls a b c) = killRange3 WhereDecls a b c

instance KillRange LetBinding where
  killRange (LetBind   i info a b c) = killRange5 LetBind i info a b c
  killRange (LetPatBind i a b       ) = killRange3 LetPatBind i a b
  killRange (LetApply   i a b c d   ) = killRange5 LetApply i a b c d
  killRange (LetOpen    i x dir     ) = killRange3 LetOpen  i x dir
  killRange (LetDeclaredVariable x)  = killRange1 LetDeclaredVariable x

instance NFData Expr
instance NFData ScopeCopyInfo
instance NFData Declaration
instance NFData ModuleApplication
instance NFData Pragma
instance NFData LetBinding
instance NFData a => NFData (Binder' a)
instance NFData LamBinding
instance NFData TypedBinding
instance NFData GeneralizeTelescope
instance NFData DataDefParams
instance NFData ProblemEq
instance NFData lhs => NFData (Clause' lhs)
instance NFData WhereDeclarations
instance NFData RHS
instance NFData SpineLHS
instance NFData LHS
instance NFData e => NFData (LHSCore' e)
instance NFData e => NFData (Pattern' e)

------------------------------------------------------------------------
-- Queries
------------------------------------------------------------------------

-- class AllNames moved to Abstract.Views.DeclaredNames

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
  anyAbstract (RecDef i _ _ _ _ _ _) = defAbstract i == AbstractDef
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
      CoConName                -> Con ux
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
    DefinedName _ x s    -> withSuffix s $ nameToExpr x  -- Can be 'isDefName', 'MacroName', 'QuotableName'.
    FieldName xs         -> Proj ProjSystem . AmbQ . fmap anameName $ xs
    ConstructorName _ xs -> Con . AmbQ . fmap anameName $ xs
    PatternSynResName xs -> PatternSyn . AmbQ . fmap anameName $ xs
    UnknownName          -> __IMPOSSIBLE__
    where
      withSuffix NoSuffix   e       = e
      withSuffix s@Suffix{} (Def x) = Def' x s
      withSuffix _          _       = __IMPOSSIBLE__

app :: Expr -> [NamedArg Expr] -> Expr
app = foldl (App defaultAppInfo_)

mkLet :: ExprInfo -> [LetBinding] -> Expr -> Expr
mkLet _ []     e = e
mkLet i (d:ds) e = Let i (d :| ds) e

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
  LitP (PatRange r) l-> Lit (ExprRange r) l
  PatternSynP _ c ps -> PatternSyn c `app` (map . fmap . fmap) patternToExpr ps
  RecP _ as          -> Rec exprNoRange $ map (Left . fmap patternToExpr) as
  EqualP{}           -> __IMPOSSIBLE__  -- Andrea TODO: where is this used?
  WithP r p          -> __IMPOSSIBLE__
  AnnP _ _ p         -> patternToExpr p

type PatternSynDefn = ([Arg Name], Pattern' Void)
type PatternSynDefns = Map QName PatternSynDefn

lambdaLiftExpr :: [Name] -> Expr -> Expr
lambdaLiftExpr ns e
  = foldr
      (\ n -> Lam exprNoRange (mkDomainFree $ defaultNamedArg $ mkBinder_ n))
      e
      ns

-- NOTE: This is only used on expressions that come from right-hand sides of pattern synonyms, and
-- thus does not have to handle all forms of expressions.
class SubstExpr a where
  substExpr :: [(Name, Expr)] -> a -> a

  default substExpr
    :: (Functor t, SubstExpr b, t b ~ a)
    => [(Name, Expr)] -> a -> a
  substExpr = fmap . substExpr

instance SubstExpr a => SubstExpr (Maybe a)
instance SubstExpr a => SubstExpr [a]
instance SubstExpr a => SubstExpr (List1 a)
instance SubstExpr a => SubstExpr (Arg a)
instance SubstExpr a => SubstExpr (Named name a)
instance SubstExpr a => SubstExpr (FieldAssignment' a)

instance (SubstExpr a, SubstExpr b) => SubstExpr (a, b) where
  substExpr s (x, y) = (substExpr s x, substExpr s y)

instance (SubstExpr a, SubstExpr b) => SubstExpr (Either a b) where
  substExpr s (Left x)  = Left (substExpr s x)
  substExpr s (Right y) = Right (substExpr s y)

instance SubstExpr C.Name where
  substExpr _ = id

instance SubstExpr ModuleName where
  substExpr _ = id

instance SubstExpr Expr where
  substExpr s e = case e of
    Var n           -> fromMaybe e (lookup n s)
    Con _           -> e
    Proj{}          -> e
    Def' _ _        -> e
    PatternSyn{}    -> e
    Lit _ _         -> e
    Underscore   _  -> e
    App  i e e'     -> App i (substExpr s e) (substExpr s e')
    Rec  i nes      -> Rec i (substExpr s nes)
    ScopedExpr si e -> ScopedExpr si (substExpr s e)
    -- The below cannot appear in pattern synonym right-hand sides
    QuestionMark{}  -> __IMPOSSIBLE__
    Dot{}           -> __IMPOSSIBLE__
    WithApp{}       -> __IMPOSSIBLE__
    Lam{}           -> __IMPOSSIBLE__
    AbsurdLam{}     -> __IMPOSSIBLE__
    ExtendedLam{}   -> __IMPOSSIBLE__
    Pi{}            -> __IMPOSSIBLE__
    Generalized{}   -> __IMPOSSIBLE__
    Fun{}           -> __IMPOSSIBLE__
    Let{}           -> __IMPOSSIBLE__
    ETel{}          -> __IMPOSSIBLE__
    RecUpdate{}     -> __IMPOSSIBLE__
    Quote{}         -> __IMPOSSIBLE__
    QuoteTerm{}     -> __IMPOSSIBLE__
    Unquote{}       -> __IMPOSSIBLE__
    DontCare{}      -> __IMPOSSIBLE__
    Macro{}         -> __IMPOSSIBLE__

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
