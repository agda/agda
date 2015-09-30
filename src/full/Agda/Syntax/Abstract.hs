{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}

{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Agda.Syntax.Internal").
-}
module Agda.Syntax.Abstract
    ( module Agda.Syntax.Abstract
    , module Agda.Syntax.Abstract.Name
    ) where

import Prelude hiding (foldl, foldr)
import Control.Arrow (first)
import Control.Applicative

import Data.Foldable as Fold
import Data.Map (Map)
import Data.Maybe
import Data.Sequence (Seq, (<|), (><))
import qualified Data.Sequence as Seq
import Data.Traversable
import Data.Typeable (Typeable)
import Data.Void

import Agda.Syntax.Concrete (FieldAssignment'(..), exprFieldA)
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Info
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Abstract.Name as A (QNamed)
import Agda.Syntax.Literal
import Agda.Syntax.Scope.Base

import Agda.Utils.Geniplate
import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible

type Args = [NamedArg Expr]

-- | Expressions after scope checking (operators parsed, names resolved).
data Expr
  = Var  Name                          -- ^ Bound variable.
  | Def  QName                         -- ^ Constant: axiom, function, data or record type.
  | Proj QName                         -- ^ Projection.
  | Con  AmbiguousQName                -- ^ Constructor.
  | PatternSyn QName                   -- ^ Pattern synonym.
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
  | App  ExprInfo Expr (NamedArg Expr) -- ^ Ordinary (binary) application.
  | WithApp ExprInfo Expr [Expr]       -- ^ With application.
  | Lam  ExprInfo LamBinding Expr      -- ^ @λ bs → e@.
  | AbsurdLam ExprInfo Hiding          -- ^ @λ()@ or @λ{}@.
  | ExtendedLam ExprInfo DefInfo QName [Clause]
  | Pi   ExprInfo Telescope Expr       -- ^ Dependent function space @Γ → A@.
  | Fun  ExprInfo (Arg Expr) Expr      -- ^ Non-dependent function space.
  | Set  ExprInfo Integer              -- ^ @Set@, @Set1@, @Set2@, ...
  | Prop ExprInfo                      -- ^ @Prop@ (no longer supported, used as dummy type).
  | Let  ExprInfo [LetBinding] Expr    -- ^ @let bs in e@.
  | ETel Telescope                     -- ^ Only used when printing telescopes.
  | Rec  ExprInfo RecordAssigns        -- ^ Record construction.
  | RecUpdate ExprInfo Expr Assigns    -- ^ Record update.
  | ScopedExpr ScopeInfo Expr          -- ^ Scope annotation.
  | QuoteGoal ExprInfo Name Expr       -- ^ Binds @Name@ to current type in @Expr@.
  | QuoteContext ExprInfo              -- ^ Returns the current context.
  | Quote ExprInfo                     -- ^ Quote an identifier 'QName'.
  | QuoteTerm ExprInfo                 -- ^ Quote a term.
  | Unquote ExprInfo                   -- ^ The splicing construct: unquote ...
  | Tactic ExprInfo Expr [NamedArg Expr] [NamedArg Expr]
                                       -- ^ @tactic e x1 .. xn | y1 | .. | yn@
  | DontCare Expr                      -- ^ For printing @DontCare@ from @Syntax.Internal@.
  deriving (Typeable, Show, Eq)

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
  deriving (Typeable, Eq, Ord, Show)

-- | Renaming (generic).
type Ren a = [(a, a)]

data Declaration
  = Axiom      Axiom DefInfo ArgInfo QName Expr      -- ^ type signature (can be irrelevant and colored, but not hidden)
  | Field      DefInfo QName (Arg Expr)              -- ^ record field
  | Primitive  DefInfo QName Expr                    -- ^ primitive function
  | Mutual     MutualInfo [Declaration]              -- ^ a bunch of mutually recursive definitions
  | Section    ModuleInfo ModuleName [TypedBindings] [Declaration]
  | Apply      ModuleInfo ModuleName ModuleApplication (Ren QName) (Ren ModuleName)
  | Import     ModuleInfo ModuleName
  | Pragma     Range      Pragma
  | Open       ModuleInfo ModuleName
    -- ^ only retained for highlighting purposes
  | FunDef     DefInfo QName Delayed [Clause] -- ^ sequence of function clauses
  | DataSig    DefInfo QName Telescope Expr -- ^ lone data signature
      -- ^ the 'LamBinding's are 'DomainFree' and binds the parameters of the datatype.
  | DataDef    DefInfo QName [LamBinding] [Constructor]
      -- ^ the 'LamBinding's are 'DomainFree' and binds the parameters of the datatype.
  | RecSig     DefInfo QName Telescope Expr -- ^ lone record signature
  | RecDef     DefInfo QName (Maybe (Ranged Induction)) (Maybe Bool) (Maybe QName) [LamBinding] Expr [Declaration]
      -- ^ The 'Expr' gives the constructor type telescope, @(x1 : A1)..(xn : An) -> Prop@,
      --   and the optional name is the constructor's name.
  | PatternSynDef QName [Arg Name] (Pattern' Void)
      -- ^ Only for highlighting purposes
  | UnquoteDecl MutualInfo DefInfo QName Expr
  | UnquoteDef  DefInfo QName Expr
  | ScopedDecl ScopeInfo [Declaration]  -- ^ scope annotation
  deriving (Typeable, Show, Eq)

class GetDefInfo a where
  getDefInfo :: a -> Maybe DefInfo

instance GetDefInfo Declaration where
  getDefInfo (Axiom _ i _ _ _)      = Just i
  getDefInfo (Field i _ _)          = Just i
  getDefInfo (Primitive i _ _)      = Just i
  getDefInfo (ScopedDecl _ (d:_))   = getDefInfo d
  getDefInfo (FunDef i _ _ _)       = Just i
  getDefInfo (DataSig i _ _ _)      = Just i
  getDefInfo (DataDef i _ _ _)      = Just i
  getDefInfo (RecSig i _ _ _)       = Just i
  getDefInfo (RecDef i _ _ _ _ _ _ _) = Just i
  getDefInfo _ = Nothing

data ModuleApplication
    = SectionApp Telescope ModuleName [NamedArg Expr]
      -- ^ @tel. M args@:  applies @M@ to @args@ and abstracts @tel@.
    | RecordModuleIFS ModuleName
      -- ^ @M {{...}}@
  deriving (Typeable, Show, Eq)

data Pragma
  = OptionsPragma [String]
  | BuiltinPragma String Expr
  | BuiltinNoDefPragma String QName
    -- ^ Builtins that do not come with a definition,
    --   but declare a name for an Agda concept.
  | RewritePragma QName
  | CompiledPragma QName String
  | CompiledExportPragma QName String
  | CompiledDeclareDataPragma QName String
  | CompiledTypePragma QName String
  | CompiledDataPragma QName String [String]
  | CompiledEpicPragma QName String
  | CompiledJSPragma QName String
  | CompiledUHCPragma QName String
  | CompiledDataUHCPragma QName String [String]
  | NoSmashingPragma QName
  | StaticPragma QName
  | DisplayPragma QName [NamedArg Pattern] Expr
  deriving (Typeable, Show, Eq)

-- | Bindings that are valid in a @let@.
data LetBinding
  = LetBind LetInfo ArgInfo Name Expr Expr
    -- ^ @LetBind info rel name type defn@
  | LetPatBind LetInfo Pattern Expr
    -- ^ Irrefutable pattern binding.
  | LetApply ModuleInfo ModuleName ModuleApplication (Ren QName) (Ren ModuleName)
    -- ^ @LetApply mi newM (oldM args) renaming moduleRenaming@.
  | LetOpen ModuleInfo ModuleName
    -- ^ only for highlighting and abstractToConcrete
  | LetDeclaredVariable Name
    -- ^ Only used for highlighting. Refers to the first occurrence of
    -- @x@ in @let x : A; x = e@.
  deriving (Typeable, Show, Eq)

-- | Only 'Axiom's.
type TypeSignature  = Declaration
type Constructor    = TypeSignature
type Field          = TypeSignature

-- | A lambda binding is either domain free or typed.
data LamBinding
  = DomainFree ArgInfo Name   -- ^ . @x@ or @{x}@ or @.x@ or @.{x}@
  | DomainFull TypedBindings  -- ^ . @(xs:e)@ or @{xs:e}@ or @(let Ds)@
  deriving (Typeable, Show, Eq)

-- | Typed bindings with hiding information.
data TypedBindings = TypedBindings Range (Arg TypedBinding)
            -- ^ . @(xs : e)@ or @{xs : e}@
  deriving (Typeable, Show, Eq)

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
  = TBind Range [WithHiding Name] Expr
    -- ^ As in telescope @(x y z : A)@ or type @(x y z : A) -> B@.
  | TLet Range [LetBinding]
    -- ^ E.g. @(let x = e)@ or @(let open M)@.
  deriving (Typeable, Show, Eq)

type Telescope  = [TypedBindings]

-- | We could throw away @where@ clauses at this point and translate them to
--   @let@. It's not obvious how to remember that the @let@ was really a
--   @where@ clause though, so for the time being we keep it here.
data Clause' lhs = Clause
  { clauseLHS        :: lhs
  , clauseRHS        :: RHS
  , clauseWhereDecls :: [Declaration]
  , clauseCatchall   :: Bool
  } deriving (Typeable, Show, Functor, Foldable, Traversable, Eq)

type Clause = Clause' LHS
type SpineClause = Clause' SpineLHS

data RHS
  = RHS Expr
  | AbsurdRHS
  | WithRHS QName [Expr] [Clause]
      -- ^ The 'QName' is the name of the with function.
  | RewriteRHS [(QName, Expr)] RHS [Declaration]
      -- ^ The 'QName's are the names of the generated with functions.
      --   One for each 'Expr'.
      --   The RHS shouldn't be another @RewriteRHS@.
  deriving (Typeable, Show, Eq)

-- | The lhs of a clause in spine view (inside-out).
--   Projection patterns are contained in @spLhsPats@,
--   represented as @DefP d []@.
data SpineLHS = SpineLHS
  { spLhsInfo     :: LHSInfo             -- ^ Range.
  , spLhsDefName  :: QName               -- ^ Name of function we are defining.
  , spLhsPats     :: [NamedArg Pattern]  -- ^ Function parameters (patterns).
  , spLhsWithPats :: [Pattern]           -- ^ @with@ patterns (after @|@).
  }
  deriving (Typeable, Show, Eq)


instance Eq LHS where
  (LHS _ core wps) == (LHS _ core' wps') = core == core' && wps == wps'

-- | The lhs of a clause in focused (projection-application) view (outside-in).
--   Projection patters are represented as 'LHSProj's.
data LHS = LHS
  { lhsInfo     :: LHSInfo               -- ^ Range.
  , lhsCore     :: LHSCore               -- ^ Copatterns.
  , lhsWithPats :: [Pattern]             -- ^ @with@ patterns (after @|@).
  }
  deriving (Typeable, Show)

-- | The lhs minus @with@-patterns in projection-application view.
--   Parameterised over the type @e@ of dot patterns.
data LHSCore' e
    -- | The head applied to ordinary patterns.
  = LHSHead  { lhsDefName  :: QName                    -- ^ Head @f@.
             , lhsPats     :: [NamedArg (Pattern' e)]  -- ^ Applied to patterns @ps@.
             }
    -- | Projection
  | LHSProj  { lhsDestructor :: QName
               -- ^ Record projection identifier.
             , lhsPatsLeft   :: [NamedArg (Pattern' e)]
               -- ^ Indices of the projection.
               --   Currently none @[]@, since we do not have indexed records.
             , lhsFocus      :: NamedArg (LHSCore' e)
               -- ^ Main branch.
             , lhsPatsRight  :: [NamedArg (Pattern' e)]
               -- ^ Further applied to patterns.
             }
  deriving (Typeable, Show, Functor, Foldable, Traversable, Eq)

type LHSCore = LHSCore' Expr

-- | Convert a focused lhs to spine view and back.
class LHSToSpine a b where
  lhsToSpine :: a -> b
  spineToLhs :: b -> a

-- | Clause instance.
instance LHSToSpine Clause SpineClause where
  lhsToSpine = fmap lhsToSpine
  spineToLhs = fmap spineToLhs

-- | List instance (for clauses).
instance LHSToSpine a b => LHSToSpine [a] [b] where
  lhsToSpine = map lhsToSpine
  spineToLhs = map spineToLhs

-- | LHS instance.
instance LHSToSpine LHS SpineLHS where
  lhsToSpine (LHS i core wps) = SpineLHS i f ps wps
    where QNamed f ps = lhsCoreToSpine core
  spineToLhs (SpineLHS i f ps wps) = LHS i (spineToLhsCore $ QNamed f ps) wps

lhsCoreToSpine :: LHSCore' e -> A.QNamed [NamedArg (Pattern' e)]
lhsCoreToSpine (LHSHead f ps) = QNamed f ps
lhsCoreToSpine (LHSProj d ps1 h ps2) = (++ (p : ps2)) <$> lhsCoreToSpine (namedArg h)
  where p = updateNamedArg (const $ DefP patNoRange d ps1) h

spineToLhsCore :: QNamed [NamedArg (Pattern' e)] -> LHSCore' e
spineToLhsCore (QNamed f ps) = lhsCoreAddSpine (LHSHead f []) ps

-- | Add applicative patterns (non-projection patterns) to the right.
lhsCoreApp :: LHSCore' e -> [NamedArg (Pattern' e)] -> LHSCore' e
lhsCoreApp (LHSHead f ps)        ps' = LHSHead f $ ps ++ ps'
lhsCoreApp (LHSProj d ps1 h ps2) ps' = LHSProj d ps1 h $ ps2 ++ ps'

-- | Add projection and applicative patterns to the right.
lhsCoreAddSpine :: LHSCore' e -> [NamedArg (Pattern' e)] -> LHSCore' e
lhsCoreAddSpine core ps = case ps2 of
    (Arg info (Named n (DefP i d ps0)) : ps2') ->
       LHSProj d ps0 (Arg info $ Named n $ lhsCoreApp core ps1) []
         `lhsCoreAddSpine` ps2'
    [] -> lhsCoreApp core ps
    _ -> __IMPOSSIBLE__
  where
    (ps1, ps2) = break (isDefP . namedArg) ps
    isDefP DefP{} = True
    isDefP _      = False

-- | Used for checking pattern linearity.
lhsCoreAllPatterns :: LHSCore' e -> [Pattern' e]
lhsCoreAllPatterns = map namedArg . qnamed . lhsCoreToSpine

-- | Used in AbstractToConcrete.
lhsCoreToPattern :: LHSCore -> Pattern
lhsCoreToPattern lc =
  case lc of
    LHSHead f aps -> DefP noInfo f aps
    LHSProj d aps1 lhscore aps2 -> DefP noInfo d $
      aps1 ++ fmap (fmap lhsCoreToPattern) lhscore : aps2
  where noInfo = patNoRange -- TODO, preserve range!

mapLHSHead :: (QName -> [NamedArg Pattern] -> LHSCore) -> LHSCore -> LHSCore
mapLHSHead f (LHSHead x ps)        = f x ps
mapLHSHead f (LHSProj d ps1 l ps2) =
  LHSProj d ps1 (fmap (fmap (mapLHSHead f)) l) ps2

---------------------------------------------------------------------------
-- * Patterns
---------------------------------------------------------------------------

-- | Parameterised over the type of dot patterns.
data Pattern' e
  = VarP Name
  | ConP ConPatInfo AmbiguousQName [NamedArg (Pattern' e)]
  | DefP PatInfo QName          [NamedArg (Pattern' e)]
    -- ^ Defined pattern: function definition @f ps@ or destructor pattern @d p ps@.
  | WildP PatInfo
    -- ^ Underscore pattern entered by user.
    --   Or generated at type checking for implicit arguments.
  | AsP PatInfo Name (Pattern' e)
  | DotP PatInfo e
  | AbsurdP PatInfo
  | LitP Literal
  | PatternSynP PatInfo QName [NamedArg (Pattern' e)]
  | RecP PatInfo [FieldAssignment' (Pattern' e)]
  deriving (Typeable, Show, Functor, Foldable, Traversable, Eq)

type Pattern  = Pattern' Expr
type Patterns = [NamedArg Pattern]

-- | Check whether we are a projection pattern.
class IsProjP a where
  isProjP :: a -> Maybe QName

instance IsProjP (Pattern' e) where
  isProjP (DefP _ d []) = Just d
  isProjP _             = Nothing

instance IsProjP a => IsProjP (Arg a) where
  isProjP = isProjP . unArg

instance IsProjP a => IsProjP (Named n a) where
  isProjP = isProjP . namedThing

{--------------------------------------------------------------------------
    Instances
 --------------------------------------------------------------------------}

instance Underscore Expr where
  underscore   = Underscore emptyMetaInfo
  isUnderscore = __IMPOSSIBLE__

instance LensHiding TypedBindings where
  getHiding   (TypedBindings _ a) = getHiding a
  mapHiding f (TypedBindings r a) = TypedBindings r $ mapHiding f a

instance LensHiding LamBinding where
  getHiding   (DomainFree ai _) = getHiding ai
  getHiding   (DomainFull tb)   = getHiding tb
  mapHiding f (DomainFree ai x) = mapHiding f ai `DomainFree` x
  mapHiding f (DomainFull tb)   = DomainFull $ mapHiding f tb

instance HasRange LamBinding where
    getRange (DomainFree _ x) = getRange x
    getRange (DomainFull b)   = getRange b

instance HasRange TypedBindings where
    getRange (TypedBindings r _) = r

instance HasRange TypedBinding where
    getRange (TBind r _ _) = r
    getRange (TLet r _)    = r

instance HasRange Expr where
    getRange (Var x)               = getRange x
    getRange (Def x)               = getRange x
    getRange (Proj x)              = getRange x
    getRange (Con x)               = getRange x
    getRange (Lit l)               = getRange l
    getRange (QuestionMark i _)    = getRange i
    getRange (Underscore  i)       = getRange i
    getRange (App i _ _)           = getRange i
    getRange (WithApp i _ _)       = getRange i
    getRange (Lam i _ _)           = getRange i
    getRange (AbsurdLam i _)       = getRange i
    getRange (ExtendedLam i _ _ _) = getRange i
    getRange (Pi i _ _)            = getRange i
    getRange (Fun i _ _)           = getRange i
    getRange (Set i _)             = getRange i
    getRange (Prop i)              = getRange i
    getRange (Let i _ _)           = getRange i
    getRange (Rec i _)             = getRange i
    getRange (RecUpdate i _ _)     = getRange i
    getRange (ETel tel)            = getRange tel
    getRange (ScopedExpr _ e)      = getRange e
    getRange (QuoteGoal _ _ e)     = getRange e
    getRange (QuoteContext i)      = getRange i
    getRange (Quote i)             = getRange i
    getRange (QuoteTerm i)         = getRange i
    getRange (Unquote i)           = getRange i
    getRange (Tactic i _ _ _)      = getRange i
    getRange (DontCare{})          = noRange
    getRange (PatternSyn x)        = getRange x
    getRange (Macro x)             = getRange x

instance HasRange Declaration where
    getRange (Axiom    _ i _ _ _    ) = getRange i
    getRange (Field      i _ _      ) = getRange i
    getRange (Mutual     i _        ) = getRange i
    getRange (Section    i _ _ _    ) = getRange i
    getRange (Apply      i _ _ _ _  ) = getRange i
    getRange (Import     i _        ) = getRange i
    getRange (Primitive  i _ _      ) = getRange i
    getRange (Pragma     i _        ) = getRange i
    getRange (Open       i _        ) = getRange i
    getRange (ScopedDecl _ d        ) = getRange d
    getRange (FunDef     i _ _ _    ) = getRange i
    getRange (DataSig    i _ _ _    ) = getRange i
    getRange (DataDef    i _ _ _    ) = getRange i
    getRange (RecSig     i _ _ _    ) = getRange i
    getRange (RecDef   i _ _ _ _ _ _ _) = getRange i
    getRange (PatternSynDef x _ _   ) = getRange x
    getRange (UnquoteDecl _ i _ _)    = getRange i
    getRange (UnquoteDef i _ _)       = getRange i

instance HasRange (Pattern' e) where
    getRange (VarP x)            = getRange x
    getRange (ConP i _ _)        = getRange i
    getRange (DefP i _ _)        = getRange i
    getRange (WildP i)           = getRange i
    getRange (AsP i _ _)         = getRange i
    getRange (DotP i _)          = getRange i
    getRange (AbsurdP i)         = getRange i
    getRange (LitP l)            = getRange l
    getRange (PatternSynP i _ _) = getRange i
    getRange (RecP i _)          = getRange i

instance HasRange SpineLHS where
    getRange (SpineLHS i _ _ _)  = getRange i

instance HasRange LHS where
    getRange (LHS i _ _)   = getRange i

instance HasRange (LHSCore' e) where
    getRange (LHSHead f ps) = fuseRange f ps
    getRange (LHSProj d ps1 lhscore ps2) = d `fuseRange` ps1 `fuseRange` lhscore `fuseRange` ps2

instance HasRange a => HasRange (Clause' a) where
    getRange (Clause lhs rhs ds catchall) = getRange (lhs,rhs,ds)

instance HasRange RHS where
    getRange AbsurdRHS                = noRange
    getRange (RHS e)                  = getRange e
    getRange (WithRHS _ e cs)         = fuseRange e cs
    getRange (RewriteRHS xes rhs wh)  = getRange (map snd xes, rhs, wh)

instance HasRange LetBinding where
    getRange (LetBind  i _ _ _ _     ) = getRange i
    getRange (LetPatBind  i _ _      ) = getRange i
    getRange (LetApply i _ _ _ _     ) = getRange i
    getRange (LetOpen  i _           ) = getRange i
    getRange (LetDeclaredVariable x)   = getRange x

-- setRange for patterns applies the range to the outermost pattern constructor
instance SetRange (Pattern' a) where
    setRange r (VarP x)             = VarP (setRange r x)
    setRange r (ConP i ns as)       = ConP (setRange r i) ns as
    setRange r (DefP _ n as)        = DefP (PatRange r) (setRange r n) as
    setRange r (WildP _)            = WildP (PatRange r)
    setRange r (AsP _ n p)          = AsP (PatRange r) (setRange r n) p
    setRange r (DotP _ e)           = DotP (PatRange r) e
    setRange r (AbsurdP _)          = AbsurdP (PatRange r)
    setRange r (LitP l)             = LitP (setRange r l)
    setRange r (PatternSynP _ n as) = PatternSynP (PatRange r) (setRange r n) as
    setRange r (RecP i as)          = RecP (PatRange r) as

instance KillRange LamBinding where
  killRange (DomainFree info x) = killRange1 (DomainFree info) x
  killRange (DomainFull b)      = killRange1 DomainFull b

instance KillRange TypedBindings where
  killRange (TypedBindings r b) = TypedBindings (killRange r) (killRange b)

instance KillRange TypedBinding where
  killRange (TBind r xs e) = killRange3 TBind r xs e
  killRange (TLet r lbs)   = killRange2 TLet r lbs

instance KillRange Expr where
  killRange (Var x)                = killRange1 Var x
  killRange (Def x)                = killRange1 Def x
  killRange (Proj x)               = killRange1 Proj x
  killRange (Con x)                = killRange1 Con x
  killRange (Lit l)                = killRange1 Lit l
  killRange (QuestionMark i ii)    = killRange2 QuestionMark i ii
  killRange (Underscore  i)        = killRange1 Underscore i
  killRange (App i e1 e2)          = killRange3 App i e1 e2
  killRange (WithApp i e es)       = killRange3 WithApp i e es
  killRange (Lam i b e)            = killRange3 Lam i b e
  killRange (AbsurdLam i h)        = killRange2 AbsurdLam i h
  killRange (ExtendedLam i n d ps) = killRange4 ExtendedLam i n d ps
  killRange (Pi i a b)             = killRange3 Pi i a b
  killRange (Fun i a b)            = killRange3 Fun i a b
  killRange (Set i n)              = killRange2 Set i n
  killRange (Prop i)               = killRange1 Prop i
  killRange (Let i ds e)           = killRange3 Let i ds e
  killRange (Rec i fs)             = killRange2 Rec i fs
  killRange (RecUpdate i e fs)     = killRange3 RecUpdate i e fs
  killRange (ETel tel)             = killRange1 ETel tel
  killRange (ScopedExpr s e)       = killRange1 (ScopedExpr s) e
  killRange (QuoteGoal i x e)      = killRange3 QuoteGoal i x e
  killRange (QuoteContext i)       = killRange1 QuoteContext i
  killRange (Quote i)              = killRange1 Quote i
  killRange (QuoteTerm i)          = killRange1 QuoteTerm i
  killRange (Unquote i)            = killRange1 Unquote i
  killRange (Tactic i e xs ys)     = killRange4 Tactic i e xs ys
  killRange (DontCare e)           = killRange1 DontCare e
  killRange (PatternSyn x)         = killRange1 PatternSyn x
  killRange (Macro x)              = killRange1 Macro x

instance KillRange Declaration where
  killRange (Axiom    p i rel a b     ) = killRange4 (Axiom p)  i rel a b
  killRange (Field      i a b         ) = killRange3 Field      i a b
  killRange (Mutual     i a           ) = killRange2 Mutual     i a
  killRange (Section    i a b c       ) = killRange4 Section    i a b c
  killRange (Apply      i a b c d     ) = killRange3 Apply      i a b c d
   -- the last two arguments of Apply are name maps, so nothing to kill
  killRange (Import     i a           ) = killRange2 Import     i a
  killRange (Primitive  i a b         ) = killRange3 Primitive  i a b
  killRange (Pragma     i a           ) = Pragma (killRange i) a
  killRange (Open       i x           ) = killRange2 Open       i x
  killRange (ScopedDecl a d           ) = killRange1 (ScopedDecl a) d
  killRange (FunDef  i a b c          ) = killRange4 FunDef  i a b c
  killRange (DataSig i a b c          ) = killRange4 DataSig i a b c
  killRange (DataDef i a b c          ) = killRange4 DataDef i a b c
  killRange (RecSig  i a b c          ) = killRange4 RecSig  i a b c
  killRange (RecDef  i a b c d e f g  ) = killRange8 RecDef  i a b c d e f g
  killRange (PatternSynDef x xs p     ) = killRange3 PatternSynDef x xs p
  killRange (UnquoteDecl mi i x e     ) = killRange4 UnquoteDecl mi i x e
  killRange (UnquoteDef i x e         ) = killRange3 UnquoteDef i x e

instance KillRange ModuleApplication where
  killRange (SectionApp a b c  ) = killRange3 SectionApp a b c
  killRange (RecordModuleIFS a ) = killRange1 RecordModuleIFS a

instance KillRange e => KillRange (Pattern' e) where
  killRange (VarP x)            = killRange1 VarP x
  killRange (ConP i a b)        = killRange3 ConP i a b
  killRange (DefP i a b)        = killRange3 DefP i a b
  killRange (WildP i)           = killRange1 WildP i
  killRange (AsP i a b)         = killRange3 AsP i a b
  killRange (DotP i a)          = killRange2 DotP i a
  killRange (AbsurdP i)         = killRange1 AbsurdP i
  killRange (LitP l)            = killRange1 LitP l
  killRange (PatternSynP i a p) = killRange3 PatternSynP i a p
  killRange (RecP i as)         = killRange2 RecP i as

instance KillRange SpineLHS where
  killRange (SpineLHS i a b c)  = killRange4 SpineLHS i a b c

instance KillRange LHS where
  killRange (LHS i a b)   = killRange3 LHS i a b

instance KillRange e => KillRange (LHSCore' e) where
  killRange (LHSHead a b)     = killRange2 LHSHead a b
  killRange (LHSProj a b c d) = killRange4 LHSProj a b c d

instance KillRange a => KillRange (Clause' a) where
  killRange (Clause lhs rhs ds catchall) = killRange4 Clause lhs rhs ds catchall

instance KillRange RHS where
  killRange AbsurdRHS                = AbsurdRHS
  killRange (RHS e)                  = killRange1 RHS e
  killRange (WithRHS q e cs)         = killRange3 WithRHS q e cs
  killRange (RewriteRHS xes rhs wh)  = killRange3 RewriteRHS xes rhs wh

instance KillRange LetBinding where
  killRange (LetBind    i info a b c) = killRange5 LetBind  i info a b c
  killRange (LetPatBind i a b       ) = killRange3 LetPatBind i a b
  killRange (LetApply   i a b c d   ) = killRange3 LetApply i a b c d
  killRange (LetOpen    i x         ) = killRange2 LetOpen  i x
  killRange (LetDeclaredVariable x)   = killRange1 LetDeclaredVariable x

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
instanceUniverseBiT' [] [t| (Declaration, RString)        |]
  -- RString is not quite what you want but we put names on lots of things...

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

instance AllNames QName where
  allNames q = Seq.singleton q

instance AllNames Declaration where
  allNames (Axiom   _ _ _ q _)        = Seq.singleton q
  allNames (Field     _   q _)        = Seq.singleton q
  allNames (Primitive _   q _)        = Seq.singleton q
  allNames (Mutual     _ defs)        = allNames defs
  allNames (DataSig _ q _ _)          = Seq.singleton q
  allNames (DataDef _ q _ decls)      = q <| allNames decls
  allNames (RecSig _ q _ _)           = Seq.singleton q
  allNames (RecDef _ q _ _ c _ _ decls) = q <| allNames c >< allNames decls
  allNames (PatternSynDef q _ _)      = Seq.singleton q
  allNames (UnquoteDecl _ _ q _)      = Seq.singleton q
  allNames (UnquoteDef _ q _)         = Seq.singleton q
  allNames (FunDef _ q _ cls)         = q <| allNames cls
  allNames (Section _ _ _ decls)      = allNames decls
  allNames Apply{}                    = Seq.empty
  allNames Import{}                   = Seq.empty
  allNames Pragma{}                   = Seq.empty
  allNames Open{}                     = Seq.empty
  allNames (ScopedDecl _ decls)       = allNames decls

instance AllNames Clause where
  allNames (Clause _ rhs decls _) = allNames rhs >< allNames decls

instance AllNames RHS where
  allNames (RHS e)                   = allNames e
  allNames AbsurdRHS{}               = Seq.empty
  allNames (WithRHS q _ cls)         = q <| allNames cls
  allNames (RewriteRHS qes rhs cls) = Seq.fromList (map fst qes) >< allNames rhs >< allNames cls

instance AllNames Expr where
  allNames Var{}                   = Seq.empty
  allNames Def{}                   = Seq.empty
  allNames Proj{}                  = Seq.empty
  allNames Con{}                   = Seq.empty
  allNames Lit{}                   = Seq.empty
  allNames QuestionMark{}          = Seq.empty
  allNames Underscore{}            = Seq.empty
  allNames (App _ e1 e2)           = allNames e1 >< allNames e2
  allNames (WithApp _ e es)        = allNames e >< allNames es
  allNames (Lam _ b e)             = allNames b >< allNames e
  allNames AbsurdLam{}             = Seq.empty
  allNames (ExtendedLam _ _ q cls) = q <| allNames cls
  allNames (Pi _ tel e)            = allNames tel >< allNames e
  allNames (Fun _ e1 e2)           = allNames e1 >< allNames e2
  allNames Set{}                   = Seq.empty
  allNames Prop{}                  = Seq.empty
  allNames (Let _ lbs e)           = allNames lbs >< allNames e
  allNames ETel{}                  = __IMPOSSIBLE__
  allNames (Rec _ fields)          = allNames [ a ^. exprFieldA | Left a <- fields ]
  allNames (RecUpdate _ e fs)      = allNames e >< allNames (map (view exprFieldA) fs)
  allNames (ScopedExpr _ e)        = allNames e
  allNames (QuoteGoal _ _ e)       = allNames e
  allNames (QuoteContext _)        = Seq.empty
  allNames Quote{}                 = Seq.empty
  allNames QuoteTerm{}             = Seq.empty
  allNames Unquote{}               = Seq.empty
  allNames (Tactic _ e xs ys)      = allNames e >< allNames xs >< allNames ys
  allNames DontCare{}              = Seq.empty
  allNames PatternSyn{}            = Seq.empty
  allNames Macro{}                 = Seq.empty

instance AllNames LamBinding where
  allNames DomainFree{}       = Seq.empty
  allNames (DomainFull binds) = allNames binds

instance AllNames TypedBindings where
  allNames (TypedBindings _ bs) = allNames bs

instance AllNames TypedBinding where
  allNames (TBind _ _ e) = allNames e
  allNames (TLet _ lbs)  = allNames lbs

instance AllNames LetBinding where
  allNames (LetBind _ _ _ e1 e2)   = allNames e1 >< allNames e2
  allNames (LetPatBind _ _ e)      = allNames e
  allNames (LetApply _ _ app _ _)  = allNames app
  allNames LetOpen{}               = Seq.empty
  allNames (LetDeclaredVariable _) = Seq.empty

instance AllNames ModuleApplication where
  allNames (SectionApp bindss _ es) = allNames bindss >< allNames es
  allNames RecordModuleIFS{}        = Seq.empty

-- | The name defined by the given axiom.
--
-- Precondition: The declaration has to be a (scoped) 'Axiom'.

axiomName :: Declaration -> QName
axiomName (Axiom _ _ _ q _)    = q
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
  anyAbstract (Axiom _ i _ _ _)      = defAbstract i == AbstractDef
  anyAbstract (Field i _ _)          = defAbstract i == AbstractDef
  anyAbstract (Mutual     _ ds)      = anyAbstract ds
  anyAbstract (ScopedDecl _ ds)      = anyAbstract ds
  anyAbstract (Section _ _ _ ds)     = anyAbstract ds
  anyAbstract (FunDef i _ _ _)       = defAbstract i == AbstractDef
  anyAbstract (DataDef i _ _ _)      = defAbstract i == AbstractDef
  anyAbstract (RecDef i _ _ _ _ _ _ _) = defAbstract i == AbstractDef
  anyAbstract (DataSig i _ _ _)      = defAbstract i == AbstractDef
  anyAbstract (RecSig i _ _ _)       = defAbstract i == AbstractDef
  anyAbstract _                      = __IMPOSSIBLE__

-- | Turn an 'AbstractName' to an expression.
nameExpr :: AbstractName -> Expr
nameExpr d = mk (anameKind d) $ anameName d
  where
    mk DefName        x = Def x
    mk FldName        x = Proj x
    mk ConName        x = Con $ AmbQ [x]
    mk PatternSynName x = PatternSyn x
    mk MacroName      x = Macro x
    mk QuotableName   x = App i (Quote i) (defaultNamedArg $ Def x)
      where i = ExprRange (getRange x)

app :: Expr -> [NamedArg Expr] -> Expr
app = foldl (App (ExprRange noRange))

mkLet :: ExprInfo -> [LetBinding] -> Expr -> Expr
mkLet i [] e = e
mkLet i ds e = Let i ds e

patternToExpr :: Pattern -> Expr
patternToExpr (VarP x)            = Var x
patternToExpr (ConP _ c ps)       =
  Con c `app` map (fmap (fmap patternToExpr)) ps
patternToExpr (DefP _ f ps)       =
  Def f `app` map (fmap (fmap patternToExpr)) ps
patternToExpr (WildP _)           = Underscore emptyMetaInfo
patternToExpr (AsP _ _ p)         = patternToExpr p
patternToExpr (DotP _ e)          = e
patternToExpr (AbsurdP _)         = Underscore emptyMetaInfo  -- TODO: could this happen?
patternToExpr (LitP l)            = Lit l
patternToExpr (PatternSynP _ _ _) = __IMPOSSIBLE__
patternToExpr (RecP _ as)         = Rec exprNoRange $ map (Left . fmap patternToExpr) as

type PatternSynDefn = ([Arg Name], Pattern' Void)
type PatternSynDefns = Map QName PatternSynDefn

lambdaLiftExpr :: [Name] -> Expr -> Expr
lambdaLiftExpr []     e = e
lambdaLiftExpr (n:ns) e = Lam (ExprRange noRange) (DomainFree defaultArgInfo n) $
                                     lambdaLiftExpr ns e

substPattern :: [(Name, Pattern)] -> Pattern -> Pattern
substPattern s p = case p of
  VarP z      -> fromMaybe p (lookup z s)
  ConP i q ps -> ConP i q (fmap (fmap (fmap (substPattern s))) ps)
  WildP i     -> p
  DotP i e    -> DotP i (substExpr (map (fmap patternToExpr) s) e)
  AbsurdP i   -> p
  LitP l      -> p
  _           -> __IMPOSSIBLE__ -- pattern synonyms (already gone) and
                                -- @-patterns (not supported anyways).

class SubstExpr a where
  substExpr :: [(Name, Expr)] -> a -> a

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
    App  i e e'           -> App i (substExpr s e) (substExpr s e')
    WithApp i e es        -> WithApp i (substExpr s e) (substExpr s es)
    Lam  i lb e           -> Lam i lb (substExpr s e)
    AbsurdLam i h         -> e
    ExtendedLam i di n cs -> __IMPOSSIBLE__   -- Maybe later...
    Pi   i t e            -> Pi i (substExpr s t) (substExpr s e)
    Fun  i ae e           -> Fun i (substExpr s ae) (substExpr s e)
    Set  i n              -> e
    Prop i                -> e
    Let  i ls e           -> Let i (substExpr s ls) (substExpr s e)
    ETel t                -> e
    Rec  i nes            -> Rec i (substExpr s nes)
    RecUpdate i e nes     -> RecUpdate i (substExpr s e) (substExpr s nes)
    -- XXX: Do we need to do more with ScopedExprs?
    ScopedExpr si e       -> ScopedExpr si (substExpr s e)
    QuoteGoal i n e       -> QuoteGoal i n (substExpr s e)
    QuoteContext i        -> e
    Quote i               -> e
    QuoteTerm i           -> e
    Unquote i             -> e
    Tactic i e xs ys      -> Tactic i (substExpr s e) (substExpr s xs) (substExpr s ys)
    DontCare e            -> DontCare (substExpr s e)
    PatternSyn{}          -> e
    Macro{}               -> e

instance SubstExpr LetBinding where
  substExpr s lb = case lb of
    LetBind i r n e e' -> LetBind i r n (substExpr s e) (substExpr s e')
    LetPatBind i p e   -> LetPatBind i p (substExpr s e) -- Andreas, 2012-06-04: what about the pattern p
    _                  -> lb -- Nicolas, 2013-11-11: what about "LetApply" there is experessions in there

instance SubstExpr TypedBindings where
  substExpr s (TypedBindings r atb) = TypedBindings r (substExpr s atb)

instance SubstExpr TypedBinding where
  substExpr s tb = case tb of
    TBind r ns e -> TBind r ns $ substExpr s e
    TLet r lbs   -> TLet r $ substExpr s lbs

-- TODO: more informative failure
insertImplicitPatSynArgs :: HasRange a => (Range -> a) -> Range -> [Arg Name] -> [NamedArg a] ->
                            Maybe ([(Name, a)], [Arg Name])
insertImplicitPatSynArgs wild r ns as = matchArgs r ns as
  where
    matchNextArg r n as@(~(a : as'))
      | matchNext n as           = return (namedArg a, as')
      | getHiding n == NotHidden = Nothing
      | otherwise                = return (wild r, as)

    matchNext _ [] = False
    matchNext n (a:as) = getHiding n == getHiding a && matchName
      where
        x = unranged $ C.nameToRawName $ nameConcrete $ unArg n
        matchName = maybe True (== x) (nameOf $ unArg a)

    matchArgs r [] []     = return ([], [])
    matchArgs r [] as     = Nothing
    matchArgs r (n:ns) [] | getHiding n == NotHidden = return ([], n : ns)    -- under-applied
    matchArgs r (n:ns) as = do
      (p, as) <- matchNextArg r n as
      first ((unArg n, p) :) <$> matchArgs (getRange p) ns as
