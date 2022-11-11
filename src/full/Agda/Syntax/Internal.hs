
module Agda.Syntax.Internal
    ( module Agda.Syntax.Internal
    , module Agda.Syntax.Internal.Blockers
    , module Agda.Syntax.Internal.Elim
    , module Agda.Syntax.Internal.Univ
    , module Agda.Syntax.Abstract.Name
    , MetaId(..), ProblemId(..)
    ) where

import Prelude hiding (null)

import Control.Monad.Identity
import Control.DeepSeq

import Data.Function (on)
import qualified Data.List as List
import Data.Maybe
import Data.Semigroup ( Semigroup, (<>), Sum(..) )

import GHC.Generics (Generic)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Concrete.Pretty (prettyHiding)
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal.Blockers
import Agda.Syntax.Internal.Elim
import Agda.Syntax.Internal.Univ
import Agda.Syntax.Common.Pretty

import Agda.Utils.CallStack
    ( CallStack
    , HasCallStack
    , prettyCallSite
    , headCallSite
    , withCallerCallStack
    )

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Null
import Agda.Utils.Size
import Agda.Utils.Tuple

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Function type domain
---------------------------------------------------------------------------

-- | Similar to 'Arg', but we need to distinguish
--   an irrelevance annotation in a function domain
--   (the domain itself is not irrelevant!)
--   from an irrelevant argument.
--
--   @Dom@ is used in 'Pi' of internal syntax, in 'Context' and 'Telescope'.
--   'Arg' is used for actual arguments ('Var', 'Con', 'Def' etc.)
--   and in 'Abstract' syntax and other situations.
--
--   [ cubical ] When @annFinite (argInfoAnnotation domInfo) = True@ for
--   the domain of a 'Pi' type, the elements should be compared by
--   tabulating the domain type.  Only supported in case the domain type
--   is primIsOne, to obtain the correct equality for partial elements.
--
data Dom' t e = Dom
  { domInfo   :: ArgInfo
  , domName   :: Maybe NamedName  -- ^ e.g. @x@ in @{x = y : A} -> B@.
  , domIsFinite :: Bool
    -- ^ Is this a Π-type (False), or a partial type (True)?
  , domTactic :: Maybe t        -- ^ "@tactic e".
  , unDom     :: e
  } deriving (Show, Functor, Foldable, Traversable)

type Dom = Dom' Term

instance Decoration (Dom' t) where
  traverseF f (Dom ai x t b a) = Dom ai x t b <$> f a

instance HasRange a => HasRange (Dom' t a) where
  getRange = getRange . unDom

instance (KillRange t, KillRange a) => KillRange (Dom' t a) where
  killRange (Dom info x t b a) = killRangeN Dom info x t b a

-- | Ignores 'Origin' and 'FreeVariables' and tactic.
instance Eq a => Eq (Dom' t a) where
  Dom (ArgInfo h1 m1 _ _ a1) s1 f1 _ x1 == Dom (ArgInfo h2 m2 _ _ a2) s2 f2 _ x2 =
    (h1, m1, a1, s1, f1, x1) == (h2, m2, a2, s2, f2, x2)

instance LensNamed (Dom' t e) where
  type NameOf (Dom' t e) = NamedName
  lensNamed f dom = f (domName dom) <&> \ nm -> dom { domName = nm }

instance LensArgInfo (Dom' t e) where
  getArgInfo        = domInfo
  setArgInfo ai dom = dom { domInfo = ai }
  mapArgInfo f  dom = dom { domInfo = f $ domInfo dom }

instance LensLock (Dom' t e) where
  getLock = getLock . getArgInfo
  setLock = mapArgInfo . setLock

-- The other lenses are defined through LensArgInfo

instance LensHiding        (Dom' t e) where
instance LensModality      (Dom' t e) where
instance LensOrigin        (Dom' t e) where
instance LensFreeVariables (Dom' t e) where
instance LensAnnotation    (Dom' t e) where

-- Since we have LensModality, we get relevance and quantity by default

instance LensRelevance (Dom' t e) where
instance LensQuantity  (Dom' t e) where
instance LensCohesion  (Dom' t e) where
instance LensModalPolarity (Dom' t e) where

argFromDom :: Dom' t a -> Arg a
argFromDom Dom{domInfo = i, unDom = a} = Arg i a

namedArgFromDom :: Dom' t a -> NamedArg a
namedArgFromDom Dom{domInfo = i, domName = s, unDom = a} = Arg i $ Named s a

-- The following functions are less general than they could be:
-- @Dom@ could be replaced by @Dom' t@.
-- However, this causes problems with instance resolution in several places.
-- often for class AddContext.

domFromArg :: Arg a -> Dom a
domFromArg (Arg i a) = Dom i Nothing False Nothing a

domFromNamedArg :: NamedArg a -> Dom a
domFromNamedArg (Arg i a) = Dom i (nameOf a) False Nothing (namedThing a)

defaultDom :: a -> Dom a
defaultDom = defaultArgDom defaultArgInfo

defaultArgDom :: ArgInfo -> a -> Dom a
defaultArgDom info x = domFromArg (Arg info x)

defaultNamedArgDom :: ArgInfo -> String -> a -> Dom a
defaultNamedArgDom info s x = (defaultArgDom info x) { domName = Just $ WithOrigin Inserted $ unranged s }

-- | Type of argument lists.
--
type Args       = [Arg Term]
type NamedArgs  = [NamedArg Term]

data DataOrRecord' p
  = IsData
  | IsRecord p
  deriving (Show, Eq, Generic)

type DataOrRecord = DataOrRecord' PatternOrCopattern

instance PatternMatchingAllowed DataOrRecord where
  patternMatchingAllowed = \case
    IsData -> True
    IsRecord patCopat -> patternMatchingAllowed patCopat

instance CopatternMatchingAllowed DataOrRecord where
  copatternMatchingAllowed = \case
    IsData -> False
    IsRecord patCopat -> copatternMatchingAllowed patCopat

-- | Store the names of the record fields in the constructor.
--   This allows reduction of projection redexes outside of TCM.
--   For instance, during substitution and application.
data ConHead = ConHead
  { conName       :: QName         -- ^ The name of the constructor.
  , conDataRecord :: DataOrRecord  -- ^ Data or record constructor?
  , conInductive  :: Induction     -- ^ Record constructors can be coinductive.
  , conFields     :: [Arg QName]   -- ^ The name of the record fields.
      --   'Arg' is stored since the info in the constructor args
      --   might not be accurate because of subtyping (issue #2170).
  } deriving (Show, Generic)

instance Eq ConHead where
  (==) = (==) `on` conName

instance Ord ConHead where
  (<=) = (<=) `on` conName

instance Pretty ConHead where
  pretty = pretty . conName

instance HasRange ConHead where
  getRange = getRange . conName

instance SetRange ConHead where
  setRange r = mapConName (setRange r)

instance CopatternMatchingAllowed ConHead where
  copatternMatchingAllowed = copatternMatchingAllowed . conDataRecord

class LensConName a where
  getConName :: a -> QName
  setConName :: QName -> a -> a
  setConName = mapConName . const
  mapConName :: (QName -> QName) -> a -> a
  mapConName f a = setConName (f (getConName a)) a

instance LensConName ConHead where
  getConName = conName
  setConName c con = con { conName = c }


-- | Raw values.
--
--   @Def@ is used for both defined and undefined constants.
--   Assume there is a type declaration and a definition for
--     every constant, even if the definition is an empty
--     list of clauses.
--
data Term = Var {-# UNPACK #-} !Int Elims -- ^ @x es@ neutral
          | Lam ArgInfo (Abs Term)        -- ^ Terms are beta normal. Relevance is ignored
          | Lit Literal
          | Def QName Elims               -- ^ @f es@, possibly a delta/iota-redex
          | Con ConHead ConInfo Elims
          -- ^ @c es@ or @record { fs = es }@
          --   @es@ allows only Apply and IApply eliminations,
          --   and IApply only for data constructors.
          | Pi (Dom Type) (Abs Type)      -- ^ dependent or non-dependent function space
          | Sort Sort
          | Level Level
          | MetaV {-# UNPACK #-} !MetaId Elims
          | DontCare Term
            -- ^ Irrelevant stuff in relevant position, but created
            --   in an irrelevant context.  Basically, an internal
            --   version of the irrelevance axiom @.irrAx : .A -> A@.
          | Dummy String Elims
            -- ^ A (part of a) term or type which is only used for internal purposes.
            --   Replaces the @Sort Prop@ hack.
            --   The @String@ typically describes the location where we create this dummy,
            --   but can contain other information as well.
            --   The second field accumulates eliminations in case we
            --   apply a dummy term to more of them. Dummy terms should never be used in places
            --   where they can affect type checking, so syntactic checks are free to ignore the
            --   eliminators, which are only there to ease debugging when a dummy term incorrectly
            --   leaks into a relevant position.
  deriving Show

type ConInfo = ConOrigin

type Elim = Elim' Term
type Elims = [Elim]  -- ^ eliminations ordered left-to-right.

-- | Binder.
--
--   'Abs': The bound variable might appear in the body.
--   'NoAbs' is pseudo-binder, it does not introduce a fresh variable,
--      similar to the @const@ of Haskell.
--
data Abs a = Abs   { absName :: ArgName, unAbs :: a }
               -- ^ The body has (at least) one free variable.
               --   Danger: 'unAbs' doesn't shift variables properly
           | NoAbs { absName :: ArgName, unAbs :: a }
  deriving (Functor, Foldable, Traversable, Generic)

instance Decoration Abs where
  traverseF f (Abs   x a) = Abs   x <$> f a
  traverseF f (NoAbs x a) = NoAbs x <$> f a

-- | Types are terms with a sort annotation.
--
data Type'' t a = El { _getSort :: Sort' t, unEl :: a }
  deriving (Show, Functor, Foldable, Traversable)

type Type' a = Type'' Term a

type Type = Type' Term

instance Decoration (Type'' t) where
  traverseF f (El s a) = El s <$> f a

class LensSort a where
  lensSort ::  Lens' a Sort
  getSort  :: a -> Sort
  getSort a = a ^. lensSort

instance LensSort Sort where
  lensSort f s = f s <&> \ s' -> s'

instance LensSort (Type' a) where
  lensSort f (El s a) = f s <&> \ s' -> El s' a

-- General instance leads to overlapping instances.
-- instance (Decoration f, LensSort a) => LensSort (f a) where
instance LensSort a => LensSort (Dom a) where
  lensSort = traverseF . lensSort

instance LensSort a => LensSort (Arg a) where
  lensSort = traverseF . lensSort


-- | Sequence of types. An argument of the first type is bound in later types
--   and so on.
data Tele a = EmptyTel
            | ExtendTel a (Abs (Tele a))  -- ^ 'Abs' is never 'NoAbs'.
  deriving (Show, Functor, Foldable, Traversable, Generic)

type Telescope = Tele (Dom Type)

data UnivSize
  = USmall  -- ^ @Prop/Set/SSet ℓ@.
  | ULarge  -- ^ @(Prop/Set/SSet)ωᵢ@.
  deriving stock (Eq, Show)

-- | Sorts.
--
data Sort' t
  = Univ Univ (Level' t)
      -- ^ @Prop ℓ@, @Set ℓ@, @SSet ℓ@.
  | Inf Univ !Integer
      -- ^ @Propωᵢ@, @(S)Setωᵢ@.
  | SizeUniv    -- ^ @SizeUniv@, a sort inhabited by type @Size@.
  | LockUniv    -- ^ @LockUniv@, a sort for locks.
  | LevelUniv   -- ^ @LevelUniv@, a sort inhabited by type @Level@. When --level-universe isn't on, this universe reduces to @Set 0@
  | IntervalUniv -- ^ @IntervalUniv@, a sort inhabited by the cubical interval.
  | PiSort (Dom' t t) (Sort' t) (Abs (Sort' t)) -- ^ Sort of the pi type.
  | FunSort (Sort' t) (Sort' t) -- ^ Sort of a (non-dependent) function type.
  | UnivSort (Sort' t) -- ^ Sort of another sort.
  | MetaS {-# UNPACK #-} !MetaId [Elim' t]
  | DefS QName [Elim' t] -- ^ A postulated sort.
  | DummyS String
    -- ^ A (part of a) term or type which is only used for internal purposes.
    --   Replaces the abuse of @Prop@ for a dummy sort.
    --   The @String@ typically describes the location where we create this dummy,
    --   but can contain other information as well.
  deriving Show

pattern Prop, Type, SSet :: Level' t -> Sort' t
pattern Prop l = Univ UProp l
pattern Type l = Univ UType l
pattern SSet l = Univ USSet l

{-# COMPLETE
  Prop, Type, SSet, Inf,
  SizeUniv, LockUniv, LevelUniv, IntervalUniv,
  PiSort, FunSort, UnivSort, MetaS, DefS, DummyS #-}

type Sort = Sort' Term

-- | Is this a strict universe inhabitable by data types?
isStrictDataSort :: Sort' t -> Bool
isStrictDataSort = \case
  Univ u _ -> univFibrancy u == IsStrict
  Inf  u _ -> univFibrancy u == IsStrict
  _ -> False


-- | A level is a maximum expression of a closed level and 0..n
--   'PlusLevel' expressions each of which is an atom plus a number.
data Level' t = Max !Integer [PlusLevel' t]
  deriving (Show, Functor, Foldable, Traversable)

type Level = Level' Term

data PlusLevel' t = Plus !Integer t
  deriving (Show, Functor, Foldable, Traversable)

type PlusLevel = PlusLevel' Term
type LevelAtom = Term

---------------------------------------------------------------------------
-- * Brave Terms
---------------------------------------------------------------------------

-- | Newtypes for terms that produce a dummy, rather than crash, when
--   applied to incompatible eliminations.
newtype BraveTerm = BraveTerm { unBrave :: Term } deriving Show

---------------------------------------------------------------------------
-- * Blocked Terms
---------------------------------------------------------------------------

type Blocked    = Blocked' Term
type NotBlocked = NotBlocked' Term
--
-- | @'Blocked a@ without the @a@.
type Blocked_ = Blocked ()

---------------------------------------------------------------------------
-- * Definitions
---------------------------------------------------------------------------

-- | Named pattern arguments.
type NAPs = [NamedArg DeBruijnPattern]

-- | A clause is a list of patterns and the clause body.
--
--  The telescope contains the types of the pattern variables and the
--  de Bruijn indices say how to get from the order the variables occur in
--  the patterns to the order they occur in the telescope. The body
--  binds the variables in the order they appear in the telescope.
--
--  @clauseTel ~ permute clausePerm (patternVars namedClausePats)@
--
--  Terms in dot patterns are valid in the clause telescope.
--
--  For the purpose of the permutation and the body dot patterns count
--  as variables. TODO: Change this!
data Clause = Clause
    { clauseLHSRange    :: Range
    , clauseFullRange   :: Range
    , clauseTel         :: Telescope
      -- ^ @Δ@: The types of the pattern variables in dependency order.
    , namedClausePats   :: NAPs
      -- ^ @Δ ⊢ ps@.  The de Bruijn indices refer to @Δ@.
    , clauseBody        :: Maybe Term
      -- ^ @Just v@ with @Δ ⊢ v@ for a regular clause, or @Nothing@ for an
      --   absurd one.
    , clauseType        :: Maybe (Arg Type)
      -- ^ @Δ ⊢ t@.  The type of the rhs under @clauseTel@.
      --   Used, e.g., by @TermCheck@.
      --   Can be 'Irrelevant' if we encountered an irrelevant projection
      --   pattern on the lhs.
    , clauseCatchall    :: Bool
      -- ^ Clause has been labelled as CATCHALL.
    , clauseRecursive   :: Maybe Bool
      -- ^ @clauseBody@ contains recursive calls; computed by termination checker.
      --   @Nothing@ means that termination checker has not run yet,
      --   or that @clauseBody@ contains meta-variables;
      --   these could be filled with recursive calls later!
      --   @Just False@ means definitely no recursive call.
      --   @Just True@ means definitely a recursive call.
    , clauseUnreachable :: Maybe Bool
      -- ^ Clause has been labelled as unreachable by the coverage checker.
      --   @Nothing@ means coverage checker has not run yet (clause may be unreachable).
      --   @Just False@ means clause is not unreachable.
      --   @Just True@ means clause is unreachable.
    , clauseEllipsis    :: ExpandedEllipsis
      -- ^ Was this clause created by expansion of an ellipsis?
    , clauseWhereModule :: Maybe ModuleName
      -- ^ Keeps track of the module name associate with the clause's where clause.
    }
  deriving (Show, Generic)

clausePats :: Clause -> [Arg DeBruijnPattern]
clausePats = map (fmap namedThing) . namedClausePats

instance HasRange Clause where
  getRange = clauseLHSRange

-- | Pattern variables.
type PatVarName = ArgName

patVarNameToString :: PatVarName -> String
patVarNameToString = argNameToString

nameToPatVarName :: Name -> PatVarName
nameToPatVarName = nameToArgName

data PatternInfo = PatternInfo
  { patOrigin :: PatOrigin
  , patAsNames :: [Name]
  } deriving (Show, Eq, Generic)

defaultPatternInfo :: PatternInfo
defaultPatternInfo = PatternInfo PatOSystem []

-- | Origin of the pattern: what did the user write in this position?
data PatOrigin
  = PatOSystem         -- ^ Pattern inserted by the system
  | PatOSplit          -- ^ Pattern generated by case split
  | PatOVar Name       -- ^ User wrote a variable pattern
  | PatODot            -- ^ User wrote a dot pattern
  | PatOWild           -- ^ User wrote a wildcard pattern
  | PatOCon            -- ^ User wrote a constructor pattern
  | PatORec            -- ^ User wrote a record pattern
  | PatOLit            -- ^ User wrote a literal pattern
  | PatOAbsurd         -- ^ User wrote an absurd pattern
  deriving (Show, Eq, Generic)

-- | Patterns are variables, constructors, or wildcards.
--   @QName@ is used in @ConP@ rather than @Name@ since
--     a constructor might come from a particular namespace.
--     This also meshes well with the fact that values (i.e.
--     the arguments we are matching with) use @QName@.
--
data Pattern' x
  = VarP PatternInfo x
    -- ^ @x@
  | DotP PatternInfo Term
    -- ^ @.t@
  | ConP ConHead ConPatternInfo [NamedArg (Pattern' x)]
    -- ^ @c ps@
    --   The subpatterns do not contain any projection copatterns.
  | LitP PatternInfo Literal
    -- ^ E.g. @5@, @"hello"@.
  | ProjP ProjOrigin QName
    -- ^ Projection copattern.  Can only appear by itself.
  | IApplyP PatternInfo Term Term x
    -- ^ Path elimination pattern, like @VarP@ but keeps track of endpoints.
  | DefP PatternInfo QName [NamedArg (Pattern' x)]
    -- ^ Used for HITs, the QName should be the one from primHComp.
  deriving (Show, Functor, Foldable, Traversable, Generic)

type Pattern = Pattern' PatVarName
    -- ^ The @PatVarName@ is a name suggestion.

varP :: a -> Pattern' a
varP = VarP defaultPatternInfo

dotP :: Term -> Pattern' a
dotP = DotP defaultPatternInfo

litP :: Literal -> Pattern' a
litP = LitP defaultPatternInfo

-- | Type used when numbering pattern variables.
data DBPatVar = DBPatVar
  { dbPatVarName  :: PatVarName
  , dbPatVarIndex :: !Int
  } deriving (Show, Eq, Generic)

type DeBruijnPattern = Pattern' DBPatVar

namedVarP :: PatVarName -> Named_ Pattern
namedVarP x = Named named $ varP x
  where named = if isUnderscore x then Nothing else Just $ WithOrigin Inserted $ unranged x

namedDBVarP :: Int -> PatVarName -> Named_ DeBruijnPattern
namedDBVarP m = (fmap . fmap) (\x -> DBPatVar x m) . namedVarP

-- | Make an absurd pattern with the given de Bruijn index.
absurdP :: Int -> DeBruijnPattern
absurdP = VarP (PatternInfo PatOAbsurd []) . DBPatVar absurdPatternName

-- | The @ConPatternInfo@ states whether the constructor belongs to
--   a record type (@True@) or data type (@False@).
--   In the former case, the @PatOrigin@ of the @conPInfo@ says
--   whether the record pattern orginates from the expansion of an
--   implicit pattern.
--   The @Type@ is the type of the whole record pattern.
--   The scope used for the type is given by any outer scope
--   plus the clause's telescope ('clauseTel').
data ConPatternInfo = ConPatternInfo
  { conPInfo   :: PatternInfo
    -- ^ Information on the origin of the pattern.
  , conPRecord :: Bool
    -- ^ @False@ if data constructor.
    --   @True@ if record constructor.
  , conPFallThrough :: Bool
    -- ^ Should the match block on non-canonical terms or can it
    --   proceed to the catch-all clause?
  , conPType   :: Maybe (Arg Type)
    -- ^ The type of the whole constructor pattern.
    --   Should be present (@Just@) if constructor pattern is
    --   is generated ordinarily by type-checking.
    --   Could be absent (@Nothing@) if pattern comes from some
    --   plugin (like Agsy).
    --   Needed e.g. for with-clause stripping.
  , conPLazy :: Bool
    -- ^ Lazy patterns are generated by the forcing translation in the unifier
    --   ('Agda.TypeChecking.Rules.LHS.Unify.unifyStep') and are dropped by
    --   the clause compiler (TODO: not yet)
    --   ('Agda.TypeChecking.CompiledClause.Compile.compileClauses') when the
    --   variables they bind are unused. The GHC backend compiles lazy matches
    --   to lazy patterns in Haskell (TODO: not yet).
  }
  deriving (Show, Generic)

noConPatternInfo :: ConPatternInfo
noConPatternInfo = ConPatternInfo defaultPatternInfo False False Nothing False

-- | Build partial 'ConPatternInfo' from 'ConInfo'
toConPatternInfo :: ConInfo -> ConPatternInfo
toConPatternInfo ConORec = noConPatternInfo{ conPInfo = PatternInfo PatORec [] , conPRecord = True }
toConPatternInfo _ = noConPatternInfo

-- | Build 'ConInfo' from 'ConPatternInfo'.
fromConPatternInfo :: ConPatternInfo -> ConInfo
fromConPatternInfo i = patToConO $ patOrigin $ conPInfo i
  where
    patToConO :: PatOrigin -> ConOrigin
    patToConO = \case
      PatOSystem -> ConOSystem
      PatOSplit  -> ConOSplit
      PatOVar{}  -> ConOSystem
      PatODot    -> ConOSystem
      PatOWild   -> ConOSystem
      PatOCon    -> ConOCon
      PatORec    -> ConORec
      PatOLit    -> ConOCon
      PatOAbsurd -> ConOSystem

-- | Extract pattern variables in left-to-right order.
--   A 'DotP' is also treated as variable (see docu for 'Clause').
class PatternVars a where
  type PatternVarOut a
  patternVars :: a -> [Arg (Either (PatternVarOut a) Term)]

instance PatternVars (Arg (Pattern' a)) where
  type PatternVarOut (Arg (Pattern' a)) = a

  -- patternVars :: Arg (Pattern' a) -> [Arg (Either a Term)]
  patternVars (Arg i (VarP _ x)   ) = [Arg i $ Left x]
  patternVars (Arg i (DotP _ t)   ) = [Arg i $ Right t]
  patternVars (Arg _ (ConP _ _ ps)) = patternVars ps
  patternVars (Arg _ (DefP _ _ ps)) = patternVars ps
  patternVars (Arg _ (LitP _ _)   ) = []
  patternVars (Arg _ ProjP{}      ) = []
  patternVars (Arg i (IApplyP _ _ _ x)) = [Arg i $ Left x]


instance PatternVars (NamedArg (Pattern' a)) where
  type PatternVarOut (NamedArg (Pattern' a)) = a

  patternVars = patternVars . fmap namedThing

instance PatternVars a => PatternVars [a] where
  type PatternVarOut [a] = PatternVarOut a

  patternVars = concatMap patternVars

-- | Retrieve the PatternInfo from a pattern
patternInfo :: Pattern' x -> Maybe PatternInfo
patternInfo (VarP i _)        = Just i
patternInfo (DotP i _)        = Just i
patternInfo (LitP i _)        = Just i
patternInfo (ConP _ ci _)     = Just $ conPInfo ci
patternInfo ProjP{}           = Nothing
patternInfo (IApplyP i _ _ _) = Just i
patternInfo (DefP i _ _)      = Just i

-- | Retrieve the origin of a pattern
patternOrigin :: Pattern' x -> Maybe PatOrigin
patternOrigin = fmap patOrigin . patternInfo

-- | Does the pattern perform a match that could fail?
properlyMatching :: Pattern' a -> Bool
properlyMatching = properlyMatching' True True

properlyMatching'
  :: Bool       -- ^ Should absurd patterns count as proper match?
  -> Bool       -- ^ Should projection patterns count as proper match?
  -> Pattern' a -- ^ The pattern.
  -> Bool
properlyMatching' absP projP = \case
  p | absP && patternOrigin p == Just PatOAbsurd -> True
  ConP _ ci ps    -- record constructors do not count as proper matches themselves
    | conPRecord ci -> List.any (properlyMatching . namedArg) ps
    | otherwise     -> True
  LitP{}    -> True
  DefP{}    -> True
  ProjP{}   -> projP
  VarP{}    -> False
  DotP{}    -> False
  IApplyP{} -> False

instance IsProjP (Pattern' a) where
  isProjP = \case
    ProjP o d -> Just (o, unambiguous d)
    _ -> Nothing

-----------------------------------------------------------------------------
-- * Explicit substitutions
-----------------------------------------------------------------------------

-- | Substitutions.

data Substitution' a

  = IdS
    -- ^ Identity substitution.
    --   @Γ ⊢ IdS : Γ@

  | EmptyS Impossible
    -- ^ Empty substitution, lifts from the empty context. First argument is @__IMPOSSIBLE__@.
    --   Apply this to closed terms you want to use in a non-empty context.
    --   @Γ ⊢ EmptyS : ()@

  | a :# Substitution' a
    -- ^ Substitution extension, ``cons''.
    --   @
    --     Γ ⊢ u : Aρ   Γ ⊢ ρ : Δ
    --     ----------------------
    --     Γ ⊢ u :# ρ : Δ, A
    --   @

  | Strengthen Impossible !Int (Substitution' a)
    -- ^ Strengthening substitution.  First argument is @__IMPOSSIBLE__@.
    --   In @'Strengthen err n ρ@ the number @n@ must be non-negative.
    --   This substitution should only be applied to values @t@ for
    --   which none of the variables @0@ up to @n - 1@ are free in
    --   @t[ρ]@, and in that case @n@ is subtracted from all free de
    --   Bruijn indices in @t[ρ]@.
    --        Γ ⊢ ρ : Δ    |Θ| = n
    --     ---------------------------
    --     Γ ⊢ Strengthen n ρ : Δ, Θ
    --   @

  | Wk !Int (Substitution' a)
    -- ^ Weakening substitution, lifts to an extended context.
    --   @
    --         Γ ⊢ ρ : Δ
    --     -------------------
    --     Γ, Ψ ⊢ Wk |Ψ| ρ : Δ
    --   @


  | Lift !Int (Substitution' a)
    -- ^ Lifting substitution.  Use this to go under a binder.
    --   @Lift 1 ρ == var 0 :# Wk 1 ρ@.
    --   @
    --            Γ ⊢ ρ : Δ
    --     -------------------------
    --     Γ, Ψρ ⊢ Lift |Ψ| ρ : Δ, Ψ
    --   @

  deriving ( Show
           , Functor
           , Foldable
           , Traversable
           , Generic
           )

type Substitution = Substitution' Term
type PatternSubstitution = Substitution' DeBruijnPattern

infixr 4 :#

instance Null (Substitution' a) where
  empty = IdS
  null IdS = True
  null _   = False


---------------------------------------------------------------------------
-- * Views
---------------------------------------------------------------------------

-- | View type as equality type.

data EqualityView
  = EqualityViewType EqualityTypeData
  | OtherType Type -- ^ reduced
  | IdiomType Type -- ^ reduced

data EqualityTypeData = EqualityTypeData
    { _eqtSort   :: Sort        -- ^ Sort of this type.
    , _eqtName   :: QName       -- ^ Builtin EQUALITY.
    , _eqtParams :: Args        -- ^ Hidden.  Empty or @Level@.
    , _eqtType   :: Arg Term    -- ^ Hidden.
    , _eqtLhs    :: Arg Term    -- ^ NotHidden.
    , _eqtRhs    :: Arg Term    -- ^ NotHidden.
    }

pattern EqualityType
  :: Sort
  -> QName
  -> Args
  -> Arg Term
  -> Arg Term
  -> Arg Term
  -> EqualityView
pattern EqualityType{ eqtSort, eqtName, eqtParams, eqtType, eqtLhs, eqtRhs } =
  EqualityViewType (EqualityTypeData eqtSort eqtName eqtParams eqtType eqtLhs eqtRhs)

{-# COMPLETE EqualityType, OtherType, IdiomType #-}

isEqualityType :: EqualityView -> Bool
isEqualityType EqualityType{} = True
isEqualityType OtherType{}    = False
isEqualityType IdiomType{}    = False

-- | View type as path type.

data PathView
  = PathType
    { pathSort  :: Sort     -- ^ Sort of this type.
    , pathName  :: QName    -- ^ Builtin PATH.
    , pathLevel :: Arg Term -- ^ Hidden
    , pathType  :: Arg Term -- ^ Hidden
    , pathLhs   :: Arg Term -- ^ NotHidden
    , pathRhs   :: Arg Term -- ^ NotHidden
    }
  | OType Type -- ^ reduced

isPathType :: PathView -> Bool
isPathType PathType{} = True
isPathType OType{}    = False

data IntervalView
      = IZero
      | IOne
      | IMin (Arg Term) (Arg Term)
      | IMax (Arg Term) (Arg Term)
      | INeg (Arg Term)
      | OTerm Term
      deriving Show

isIOne :: IntervalView -> Bool
isIOne IOne = True
isIOne _ = False

---------------------------------------------------------------------------
-- * Absurd Lambda
---------------------------------------------------------------------------

-- | Absurd lambdas are internally represented as identity
--   with variable name "()".
absurdBody :: Abs Term
absurdBody = Abs absurdPatternName $ Var 0 []

isAbsurdBody :: Abs Term -> Bool
isAbsurdBody (Abs x (Var 0 [])) = isAbsurdPatternName x
isAbsurdBody _                  = False

absurdPatternName :: PatVarName
absurdPatternName = "()"

isAbsurdPatternName :: PatVarName -> Bool
isAbsurdPatternName x = x == absurdPatternName

---------------------------------------------------------------------------
-- * Smart constructors
---------------------------------------------------------------------------

-- | An unapplied variable.
var :: Nat -> Term
var i | i >= 0    = Var i []
      | otherwise = __IMPOSSIBLE__

-- | Add 'DontCare' is it is not already a @DontCare@.
dontCare :: Term -> Term
dontCare v =
  case v of
    DontCare{} -> v
    _          -> DontCare v

type DummyTermKind = String

-- | Construct a string representing the call-site that created the dummy thing.
dummyLocName :: CallStack -> String
dummyLocName cs = maybe __IMPOSSIBLE__ prettyCallSite (headCallSite cs)

-- | Aux: A dummy term to constitute a dummy term/level/sort/type.
dummyTermWith :: DummyTermKind -> CallStack -> Term
dummyTermWith kind cs = flip Dummy [] $ concat [kind, ": ", dummyLocName cs]

-- | A dummy level to constitute a level/sort created at location.
--   Note: use macro __DUMMY_LEVEL__ !
dummyLevel :: CallStack -> Level
dummyLevel = atomicLevel . dummyTermWith "dummyLevel"

-- | A dummy term created at location.
--   Note: use macro __DUMMY_TERM__ !
dummyTerm :: CallStack -> Term
dummyTerm = dummyTermWith "dummyTerm"

__DUMMY_TERM__ :: HasCallStack => Term
__DUMMY_TERM__ = withCallerCallStack dummyTerm

__DUMMY_LEVEL__ :: HasCallStack => Level
__DUMMY_LEVEL__ = withCallerCallStack dummyLevel

-- | A dummy sort created at location.
--   Note: use macro __DUMMY_SORT__ !
dummySort :: CallStack -> Sort
dummySort = DummyS . dummyLocName

__DUMMY_SORT__ :: HasCallStack => Sort
__DUMMY_SORT__ = withCallerCallStack dummySort

-- | A dummy type created at location.
--   Note: use macro __DUMMY_TYPE__ !
dummyType :: CallStack -> Type
dummyType cs = El (dummySort cs) $ dummyTermWith "dummyType" cs

__DUMMY_TYPE__ :: HasCallStack => Type
__DUMMY_TYPE__ = withCallerCallStack dummyType

-- | Context entries without a type have this dummy type.
--   Note: use macro __DUMMY_DOM__ !
dummyDom :: CallStack -> Dom Type
dummyDom = defaultDom . dummyType

__DUMMY_DOM__ :: HasCallStack => Dom Type
__DUMMY_DOM__ = withCallerCallStack dummyDom

-- | Constant level @n@
pattern ClosedLevel :: Integer -> Level
pattern ClosedLevel n = Max n []

atomicLevel :: t -> Level' t
atomicLevel a = Max 0 [ Plus 0 a ]

varSort :: Int -> Sort
varSort n = Type $ atomicLevel $ var n

tmSort :: Term -> Sort
tmSort t = Type $ atomicLevel t

tmSSort :: Term -> Sort
tmSSort t = SSet $ atomicLevel t

-- | Given a constant @m@ and level @l@, compute @m + l@
levelPlus :: Integer -> Level -> Level
levelPlus m (Max n as) = Max (m + n) $ map pplus as
  where pplus (Plus n l) = Plus (m + n) l

levelSuc :: Level -> Level
levelSuc = levelPlus 1

mkType :: Integer -> Sort
mkType n = Type $ ClosedLevel n

mkProp :: Integer -> Sort
mkProp n = Prop $ ClosedLevel n

mkSSet :: Integer -> Sort
mkSSet n = SSet $ ClosedLevel n

isSort :: Term -> Maybe Sort
isSort = \case
  Sort s -> Just s
  _      -> Nothing

impossibleTerm :: CallStack -> Term
impossibleTerm = flip Dummy [] . show . Impossible

---------------------------------------------------------------------------
-- * Telescopes.
---------------------------------------------------------------------------

-- | A traversal for the names in a telescope.
mapAbsNamesM :: Applicative m => (ArgName -> m ArgName) -> Tele a -> m (Tele a)
mapAbsNamesM f EmptyTel                  = pure EmptyTel
mapAbsNamesM f (ExtendTel a (  Abs x b)) = ExtendTel a <$> (  Abs <$> f x <*> mapAbsNamesM f b)
mapAbsNamesM f (ExtendTel a (NoAbs x b)) = ExtendTel a <$> (NoAbs <$> f x <*> mapAbsNamesM f b)
  -- Ulf, 2013-11-06: Last case is really impossible but I'd rather find out we
  --                  violated that invariant somewhere other than here.

mapAbsNames :: (ArgName -> ArgName) -> Tele a -> Tele a
mapAbsNames f = runIdentity . mapAbsNamesM (Identity . f)

-- Ulf, 2013-11-06
-- The record parameter is named "" inside the record module so we can avoid
-- printing it (issue 208), but we don't want that to show up in the type of
-- the functions in the module (issue 892). This function is used on the record
-- module telescope before adding it to a type in
-- TypeChecking.Monad.Signature.addConstant (to handle functions defined in
-- record modules) and TypeChecking.Rules.Record.checkProjection (to handle
-- record projections).
replaceEmptyName :: ArgName -> Tele a -> Tele a
replaceEmptyName x = mapAbsNames $ \ y -> if null y then x else y

-- | Telescope as list.
type ListTel' a = [Dom (a, Type)]
type ListTel = ListTel' ArgName

telFromList' :: (a -> ArgName) -> ListTel' a -> Telescope
telFromList' f = List.foldr extTel EmptyTel
  where
    extTel dom@Dom{unDom = (x, a)} = ExtendTel (dom{unDom = a}) . Abs (f x)

-- | Convert a list telescope to a telescope.
telFromList :: ListTel -> Telescope
telFromList = telFromList' id

-- | Convert a telescope to its list form.
telToList :: Tele (Dom t) -> [Dom (ArgName,t)]
telToList EmptyTel                    = []
telToList (ExtendTel arg (Abs x tel)) = fmap (x,) arg : telToList tel
telToList (ExtendTel _    NoAbs{}   ) = __IMPOSSIBLE__

-- | Lens to edit a 'Telescope' as a list.
listTel :: Lens' Telescope ListTel
listTel f = fmap telFromList . f . telToList

-- | Drop the types from a telescope.
class TelToArgs a where
  telToArgs :: a -> [Arg ArgName]

instance TelToArgs ListTel where
  telToArgs = map $ \ dom -> Arg (domInfo dom) (fst $ unDom dom)

instance TelToArgs Telescope where
  telToArgs = telToArgs . telToList

-- | Constructing a singleton telescope.
class SgTel a where
  sgTel :: a -> Telescope

instance SgTel (ArgName, Dom Type) where
  sgTel (x, !dom) = ExtendTel dom $ Abs x EmptyTel

instance SgTel (Dom (ArgName, Type)) where
  sgTel dom = ExtendTel (snd <$> dom) $ Abs (fst $ unDom dom) EmptyTel

instance SgTel (Dom Type) where
  sgTel dom = sgTel (stringToArgName "_", dom)

---------------------------------------------------------------------------
-- * Simple operations on terms and types.
---------------------------------------------------------------------------

-- | Removing a topmost 'DontCare' constructor.
stripDontCare :: Term -> Term
stripDontCare = \case
  DontCare v -> v
  v          -> v

-- | Doesn't do any reduction.
arity :: Type -> Nat
arity t = case unEl t of
  Pi  _ b -> 1 + arity (unAbs b)
  _       -> 0

-- | Suggest a name if available (i.e. name is not "_")
class Suggest a where
  suggestName :: a -> Maybe String

instance Suggest String where
  suggestName "_" = Nothing
  suggestName  x  = Just x

instance Suggest (Abs b) where
  suggestName = suggestName . absName

instance Suggest Name where
  suggestName = suggestName . nameToArgName

instance Suggest Term where
  suggestName (Lam _ v) = suggestName v
  suggestName _         = Nothing

-- Wrapping @forall a. (Suggest a) => a@ into a datatype because
-- GHC doesn't support impredicative polymorphism
data Suggestion = forall a. Suggest a => Suggestion a

suggests :: [Suggestion] -> String
suggests []     = "x"
suggests (Suggestion x : xs) = fromMaybe (suggests xs) $ suggestName x

---------------------------------------------------------------------------
-- * Eliminations.
---------------------------------------------------------------------------

-- | Convert top-level postfix projections into prefix projections.
unSpine :: Term -> Term
unSpine = unSpine' $ \_ _ -> True

-- | Convert 'Proj' projection eliminations
--   according to their 'ProjOrigin' into
--   'Def' projection applications.
unSpine' :: (ProjOrigin -> QName -> Bool) -> Term -> Term
unSpine' p v =
  case hasElims v of
    Just (h, es) -> loop h [] es
    Nothing      -> v
  where
    loop :: (Elims -> Term) -> Elims -> Elims -> Term
    loop h res es =
      case es of
        []                     -> v
        Proj o f : es' | p o f -> loop (Def f) [Apply (defaultArg v)] es'
        e        : es'         -> loop h (e : res) es'
      where v = h $ reverse res

-- | A view distinguishing the neutrals @Var@, @Def@, and @MetaV@ which
--   can be projected.
hasElims :: Term -> Maybe (Elims -> Term, Elims)
hasElims v =
  case v of
    Var   i es -> Just (Var   i, es)
    Def   f es -> Just (Def   f, es)
    MetaV x es -> Just (MetaV x, es)
    Con{}      -> Nothing
    Lit{}      -> Nothing
    Lam{}      -> Nothing
    Pi{}       -> Nothing
    Sort{}     -> Nothing
    Level{}    -> Nothing
    DontCare{} -> Nothing
    Dummy{}    -> Nothing

---------------------------------------------------------------------------
-- * Type family for type-directed operations.
---------------------------------------------------------------------------

-- @TypeOf a@ contains sufficient type information to do
-- a type-directed traversal of @a@.
type family TypeOf a

type instance TypeOf Term        = Type                  -- Type of the term
type instance TypeOf Elims       = (Type, Elims -> Term) -- Head symbol type + constructor
type instance TypeOf (Abs Term)  = (Dom Type, Abs Type)  -- Domain type + codomain type
type instance TypeOf (Abs Type)  = Dom Type              -- Domain type
type instance TypeOf (Arg a)     = Dom (TypeOf a)
type instance TypeOf (Dom a)     = TypeOf a
type instance TypeOf Type        = ()
type instance TypeOf Sort        = ()
type instance TypeOf Level       = ()
type instance TypeOf [PlusLevel] = ()
type instance TypeOf PlusLevel   = ()

---------------------------------------------------------------------------
-- * Null instances.
---------------------------------------------------------------------------

instance Null (Tele a) where
  empty = EmptyTel
  null EmptyTel    = True
  null ExtendTel{} = False

-- | A 'null' clause is one with no patterns and no rhs.
--   Should not exist in practice.
instance Null Clause where
  empty = Clause empty empty empty empty empty empty False Nothing Nothing empty empty
  null (Clause _ _ tel pats body _ _ _ _ _ wm)
    =  null tel
    && null pats
    && null body
    && null wm


---------------------------------------------------------------------------
-- * Show instances.
---------------------------------------------------------------------------

instance Show a => Show (Abs a) where
  showsPrec p (Abs x a) = showParen (p > 0) $
    showString "Abs " . shows x . showString " " . showsPrec 10 a
  showsPrec p (NoAbs x a) = showParen (p > 0) $
    showString "NoAbs " . shows x . showString " " . showsPrec 10 a

-- instance Show t => Show (Blocked t) where
--   showsPrec p (Blocked m x) = showParen (p > 0) $
--     showString "Blocked " . shows m . showString " " . showsPrec 10 x
--   showsPrec p (NotBlocked x) = showsPrec p x

---------------------------------------------------------------------------
-- * Sized instances and TermSize.
---------------------------------------------------------------------------

-- | The size of a telescope is its length (as a list).
instance Sized (Tele a) where
  size  EmptyTel         = 0
  size (ExtendTel _ tel) = 1 + size tel

  natSize EmptyTel          = Zero
  natSize (ExtendTel _ tel) = Succ $ natSize tel

instance Sized a => Sized (Abs a) where
  size    = size    . unAbs
  natSize = natSize . unAbs

-- | The size of a term is roughly the number of nodes in its
--   syntax tree.  This number need not be precise for logical
--   correctness of Agda, it is only used for reporting
--   (and maybe decisions regarding performance).
--
--   Not counting towards the term size are:
--
--     * sort and color annotations,
--     * projections.
--
class TermSize a where
  termSize :: a -> Int
  termSize = getSum . tsize

  tsize :: a -> Sum Int

instance {-# OVERLAPPABLE #-} (Foldable t, TermSize a) => TermSize (t a) where
  tsize = foldMap tsize

instance TermSize Term where
  tsize = \case
    Var _ vs    -> 1 + tsize vs
    Def _ vs    -> 1 + tsize vs
    Con _ _ vs    -> 1 + tsize vs
    MetaV _ vs  -> 1 + tsize vs
    Level l     -> tsize l
    Lam _ f     -> 1 + tsize f
    Lit _       -> 1
    Pi a b      -> 1 + tsize a + tsize b
    Sort s      -> tsize s
    DontCare mv -> tsize mv
    Dummy{}     -> 1

instance TermSize Sort where
  tsize = \case
    Univ _ l  -> 1 + tsize l
    Inf _ _   -> 1
    SizeUniv  -> 1
    LockUniv  -> 1
    LevelUniv -> 1
    IntervalUniv -> 1
    PiSort a s1 s2 -> 1 + tsize a + tsize s1 + tsize s2
    FunSort s1 s2 -> 1 + tsize s1 + tsize s2
    UnivSort s -> 1 + tsize s
    MetaS _ es -> 1 + tsize es
    DefS _ es  -> 1 + tsize es
    DummyS{}   -> 1

instance TermSize Level where
  tsize (Max _ as) = 1 + tsize as

instance TermSize PlusLevel where
  tsize (Plus _ a)      = tsize a

instance TermSize a => TermSize (Substitution' a) where
  tsize IdS                  = 1
  tsize (EmptyS _)           = 1
  tsize (Wk _ rho)           = 1 + tsize rho
  tsize (t :# rho)           = 1 + tsize t + tsize rho
  tsize (Strengthen _ _ rho) = 1 + tsize rho
  tsize (Lift _ rho)         = 1 + tsize rho

---------------------------------------------------------------------------
-- * KillRange instances.
---------------------------------------------------------------------------

instance KillRange DataOrRecord where
  killRange = id

instance KillRange ConHead where
  killRange (ConHead c d i fs) = killRangeN ConHead c d i fs

instance KillRange Term where
  killRange = \case
    Var i vs    -> killRangeN (Var i) vs
    Def c vs    -> killRangeN Def c vs
    Con c ci vs -> killRangeN Con c ci vs
    MetaV m vs  -> killRangeN (MetaV m) vs
    Lam i f     -> killRangeN Lam i f
    Lit l       -> killRangeN Lit l
    Level l     -> killRangeN Level l
    Pi a b      -> killRangeN Pi a b
    Sort s      -> killRangeN Sort s
    DontCare mv -> killRangeN DontCare mv
    v@Dummy{}   -> v

instance KillRange Level where
  killRange (Max n as) = killRangeN (Max n) as

instance KillRange PlusLevel where
  killRange (Plus n l) = killRangeN (Plus n) l

instance (KillRange a) => KillRange (Type' a) where
  killRange (El s v) = killRangeN El s v

instance KillRange Sort where
  killRange = \case
    Inf u n    -> Inf u n
    SizeUniv   -> SizeUniv
    LockUniv   -> LockUniv
    LevelUniv  -> LevelUniv
    IntervalUniv -> IntervalUniv
    Univ u a   -> killRangeN (Univ u) a
    PiSort a s1 s2 -> killRangeN PiSort a s1 s2
    FunSort s1 s2 -> killRangeN FunSort s1 s2
    UnivSort s -> killRangeN UnivSort s
    MetaS x es -> killRangeN (MetaS x) es
    DefS d es  -> killRangeN DefS d es
    s@DummyS{} -> s

instance KillRange Substitution where
  killRange IdS                    = IdS
  killRange (EmptyS err)           = EmptyS err
  killRange (Wk n rho)             = killRangeN (Wk n) rho
  killRange (t :# rho)             = killRangeN (:#) t rho
  killRange (Strengthen err n rho) = killRangeN (Strengthen err n) rho
  killRange (Lift n rho)           = killRangeN (Lift n) rho

instance KillRange PatOrigin where
  killRange = id

instance KillRange PatternInfo where
  killRange (PatternInfo o xs) = killRangeN PatternInfo o xs

instance KillRange ConPatternInfo where
  killRange (ConPatternInfo i mr b mt lz) = killRangeN (ConPatternInfo i mr b) mt lz

instance KillRange DBPatVar where
  killRange (DBPatVar x i) = killRangeN DBPatVar x i

instance KillRange a => KillRange (Pattern' a) where
  killRange p =
    case p of
      VarP o x         -> killRangeN VarP o x
      DotP o v         -> killRangeN DotP o v
      ConP con info ps -> killRangeN ConP con info ps
      LitP o l         -> killRangeN LitP o l
      ProjP o q        -> killRangeN (ProjP o) q
      IApplyP o u t x  -> killRangeN (IApplyP o) u t x
      DefP o q ps      -> killRangeN (DefP o) q ps

instance KillRange Clause where
  killRange (Clause rl rf tel ps body t catchall recursive unreachable ell wm) =
    killRangeN Clause rl rf tel ps body t catchall recursive unreachable ell wm

instance KillRange a => KillRange (Tele a) where
  killRange = fmap killRange

instance KillRange a => KillRange (Blocked a) where
  killRange = fmap killRange

instance KillRange a => KillRange (Abs a) where
  killRange = fmap killRange

-----------------------------------------------------------------------------
-- * Simple pretty printing
-----------------------------------------------------------------------------

instance Pretty a => Pretty (Substitution' a) where
  prettyPrec = pr
    where
    pr p rho = case rho of
      IdS                -> "idS"
      EmptyS err         -> "emptyS"
      t :# rho           -> mparens (p > 2) $
                            sep [ pr 2 rho <> ",", prettyPrec 3 t ]
      Strengthen _ n rho -> mparens (p > 9) $
                            text ("strS " ++ show n) <+> pr 10 rho
      Wk n rho           -> mparens (p > 9) $
                            text ("wkS " ++ show n) <+> pr 10 rho
      Lift n rho         -> mparens (p > 9) $
                            text ("liftS " ++ show n) <+> pr 10 rho

instance Pretty Term where
  prettyPrec p v =
    case v of
      Var x els -> text ("@" ++ show x) `pApp` els
      Lam ai b   ->
        mparens (p > 0) $
        sep [ "λ" <+> prettyHiding ai id (text . absName $ b) <+> "->"
            , nest 2 $ pretty (unAbs b) ]
      Lit l                -> pretty l
      Def q els            -> pretty q `pApp` els
      Con c ci vs          -> pretty (conName c) `pApp` vs
      Pi a (NoAbs _ b)     -> mparens (p > 0) $
        sep [ pretty (getModality a) <+> prettyPrec 1 (unDom a) <+> "->"
            , nest 2 $ pretty b ]
      Pi a b               -> mparens (p > 0) $
        sep [ pDom (domInfo a) (pretty (getModality a) <+> text (absName b) <+> ":" <+> pretty (unDom a)) <+> "->"
            , nest 2 $ pretty (unAbs b) ]
      Sort s      -> prettyPrec p s
      Level l     -> prettyPrec p l
      MetaV x els -> pretty x `pApp` els
      DontCare v  -> prettyPrec p v
      Dummy s es  -> parens (text s) `pApp` es
    where
      pApp d els = mparens (not (null els) && p > 9) $
                   sep [d, nest 2 $ fsep (map (prettyPrec 10) els)]

instance Pretty t => Pretty (Abs t) where
  pretty (Abs   x t) = "Abs"   <+> (text x <> ".") <+> pretty t
  pretty (NoAbs x t) = "NoAbs" <+> (text x <> ".") <+> pretty t

instance (Pretty t, Pretty e) => Pretty (Dom' t e) where
  pretty dom = pLock <+> pTac <+> pDom dom (pretty (getModality dom) <+> pretty (unDom dom))
    where
      pTac | Just t <- domTactic dom = "@" <> parens ("tactic" <+> pretty t)
           | otherwise               = empty
      pLock | IsLock{} <- getLock dom = "@lock"
            | otherwise = empty

pDom :: LensHiding a => a -> Doc -> Doc
pDom i =
  case getHiding i of
    NotHidden  -> parens
    Hidden     -> braces
    Instance{} -> braces . braces

instance Pretty Clause where
  pretty Clause{clauseTel = tel, namedClausePats = ps, clauseBody = b, clauseType = t} =
    sep [ pretty tel <+> "|-"
        , nest 2 $ sep [ fsep (map (prettyPrec 10) ps) <+> "="
                       , nest 2 $ pBody b t ] ]
    where
      pBody Nothing _ = "(absurd)"
      pBody (Just b) Nothing  = pretty b
      pBody (Just b) (Just t) = sep [ pretty b <+> ":", nest 2 $ pretty t ]

instance Pretty a => Pretty (Tele (Dom a)) where
  pretty tel = fsep [ pDom a (text x <+> ":" <+> pretty (unDom a)) | (x, a) <- telToList tel ]
    where
      telToList EmptyTel = []
      telToList (ExtendTel a tel) = (absName tel, a) : telToList (unAbs tel)

prettyPrecLevelSucs :: Int -> Integer -> (Int -> Doc) -> Doc
prettyPrecLevelSucs p 0 d = d p
prettyPrecLevelSucs p n d = mparens (p > 9) $ "lsuc" <+> prettyPrecLevelSucs 10 (n - 1) d

instance Pretty Level where
  prettyPrec p (Max n as) =
    case as of
      []  -> prettyN
      [a] | n == 0 -> prettyPrec p a
      _   -> mparens (p > 9) $ List.foldr1 (\a b -> "lub" <+> a <+> b) $
        [ prettyN | n > 0 ] ++ map (prettyPrec 10) as
    where
      prettyN = prettyPrecLevelSucs p n (const "lzero")

instance Pretty PlusLevel where
  prettyPrec p (Plus n a) = prettyPrecLevelSucs p n $ \p -> prettyPrec p a

instance Pretty Sort where
  prettyPrec p s =
    case s of
      Univ u (ClosedLevel n) -> text $ suffix n $ showUniv u
      Univ u l -> mparens (p > 9) $ text (showUniv u) <+> prettyPrec 10 l
      Inf u n -> text $ suffix n $ showUniv u ++ "ω"
      SizeUniv -> "SizeUniv"
      LockUniv -> "LockUniv"
      LevelUniv -> "LevelUniv"
      IntervalUniv -> "IntervalUniv"
      PiSort a s1 s2 -> mparens (p > 9) $
        "piSort" <+> pDom (domInfo a) (text (absName s2) <+> ":" <+> pretty (unDom a) <+> ":" <+> pretty s1)
                      <+> parens (pretty (unAbs s2))
      FunSort a b -> mparens (p > 9) $
        "funSort" <+> prettyPrec 10 a <+> prettyPrec 10 b
      UnivSort s -> mparens (p > 9) $ "univSort" <+> prettyPrec 10 s
      MetaS x es -> prettyPrec p $ MetaV x es
      DefS d es  -> prettyPrec p $ Def d es
      DummyS s   -> parens $ text s
   where
     suffix n = applyWhen (n /= 0) (++ show n)

instance Pretty Type where
  prettyPrec p (El _ a) = prettyPrec p a

instance Pretty DBPatVar where
  prettyPrec _ x = text $ patVarNameToString (dbPatVarName x) ++ "@" ++ show (dbPatVarIndex x)

instance Pretty a => Pretty (Pattern' a) where
  prettyPrec n (VarP _o x)   = prettyPrec n x
  prettyPrec _ (DotP _o t)   = "." <> prettyPrec 10 t
  prettyPrec n (ConP c i nps)= mparens (n > 0 && not (null nps)) $
    (lazy <> pretty (conName c)) <+> fsep (map (prettyPrec 10) ps)
    where ps = map (fmap namedThing) nps
          lazy | conPLazy i = "~"
               | otherwise  = empty
  prettyPrec n (DefP o q nps)= mparens (n > 0 && not (null nps)) $
    pretty q <+> fsep (map (prettyPrec 10) ps)
    where ps = map (fmap namedThing) nps
  -- -- Version with printing record type:
  -- prettyPrec _ (ConP c i ps) = (if b then braces else parens) $ prTy $
  --   text (show $ conName c) <+> fsep (map (pretty . namedArg) ps)
  --   where
  --     b = maybe False (== ConOSystem) $ conPRecord i
  --     prTy d = caseMaybe (conPType i) d $ \ t -> d  <+> ":" <+> pretty t
  prettyPrec _ (LitP _ l)    = pretty l
  prettyPrec _ (ProjP _o q)  = text ("." ++ prettyShow q)
  prettyPrec n (IApplyP _o _ _ x) = prettyPrec n x
--  prettyPrec n (IApplyP _o u0 u1 x) = text "@[" <> prettyPrec 0 u0 <> text ", " <> prettyPrec 0 u1 <> text "]" <> prettyPrec n x

instance Pretty a => Pretty (Blocked a) where
  pretty = \case
    NotBlocked ReallyNotBlocked a -> pretty a
    NotBlocked nb a -> pretty a <+> ("[ blocked on" <+> pretty nb <+> "]")
    Blocked     b a -> pretty a <+> ("[ stuck on" <+> pretty  b <+> "]")

-----------------------------------------------------------------------------
-- * NFData instances
-----------------------------------------------------------------------------

-- Note: only strict in the shape of the terms.

instance NFData Term where
  rnf = \case
    Var _ es   -> rnf es
    Lam _ b    -> rnf (unAbs b)
    Lit l      -> rnf l
    Def _ es   -> rnf es
    Con _ _ vs -> rnf vs
    Pi a b     -> rnf (unDom a, unAbs b)
    Sort s     -> rnf s
    Level l    -> rnf l
    MetaV _ es -> rnf es
    DontCare v -> rnf v
    Dummy _ es -> rnf es

instance NFData Type where
  rnf (El s v) = rnf (s, v)

instance NFData Sort where
  rnf = \case
    Univ _ l   -> rnf l
    Inf _ _  -> ()
    SizeUniv -> ()
    LockUniv -> ()
    LevelUniv -> ()
    IntervalUniv -> ()
    PiSort a b c -> rnf (a, b, unAbs c)
    FunSort a b -> rnf (a, b)
    UnivSort a -> rnf a
    MetaS _ es -> rnf es
    DefS _ es  -> rnf es
    DummyS _   -> ()

instance NFData Level where
  rnf (Max n as) = rnf (n, as)

instance NFData PlusLevel where
  rnf (Plus n l) = rnf (n, l)

instance NFData e => NFData (Dom e) where
  rnf (Dom a c d e f) = rnf a `seq` rnf c `seq` rnf d `seq` rnf e `seq` rnf f

instance NFData DataOrRecord
instance NFData ConHead
instance NFData a => NFData (Abs a)
instance NFData a => NFData (Tele a)
instance NFData IsFibrant
instance NFData Clause
instance NFData PatternInfo
instance NFData PatOrigin
instance NFData x => NFData (Pattern' x)
instance NFData DBPatVar
instance NFData ConPatternInfo
instance NFData a => NFData (Substitution' a)
