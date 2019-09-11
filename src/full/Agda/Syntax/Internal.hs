{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE UndecidableInstances       #-}  -- because of shortcomings of FunctionalDependencies

module Agda.Syntax.Internal
    ( module Agda.Syntax.Internal
    , module Agda.Syntax.Abstract.Name
    , MetaId(..)
    ) where

import Prelude hiding (foldr, mapM, null)
import GHC.Stack (HasCallStack, freezeCallStack, callStack)

import Control.Monad.Identity hiding (mapM)
import Control.DeepSeq

import Data.Foldable ( Foldable, foldMap )
import Data.Function
import qualified Data.List as List
import Data.Maybe
import Data.Monoid ( Monoid, mempty, mappend )
import Data.Semigroup ( Semigroup, (<>), Sum(..) )

import Data.Traversable
import Data.Data (Data)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Concrete.Pretty (prettyHiding)
import Agda.Syntax.Abstract.Name

import Agda.Utils.Empty

import Agda.Utils.Functor
import Agda.Utils.Geniplate
import Agda.Utils.Lens
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Pretty
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
--   [ cubical ] When @domFinite = True@ for the domain of a 'Pi'
--   type, the elements should be compared by tabulating the domain type.
--   Only supported in case the domain type is primIsOne, to obtain
--   the correct equality for partial elements.
--
data Dom' t e = Dom
  { domInfo   :: ArgInfo
  , domFinite :: !Bool
  , domName   :: Maybe NamedName  -- ^ e.g. @x@ in @{x = y : A} -> B@.
  , domTactic :: Maybe t        -- ^ "@tactic e".
  , unDom     :: e
  } deriving (Data, Show, Functor, Foldable, Traversable)

type Dom = Dom' Term

instance Decoration (Dom' t) where
  traverseF f (Dom ai b x t a) = Dom ai b x t <$> f a

instance HasRange a => HasRange (Dom' t a) where
  getRange = getRange . unDom

instance (KillRange t, KillRange a) => KillRange (Dom' t a) where
  killRange (Dom info b x t a) = killRange5 Dom info b x t a

-- | Ignores 'Origin' and 'FreeVariables' and tactic.
instance Eq a => Eq (Dom' t a) where
  Dom (ArgInfo h1 m1 _ _) b1 s1 _ x1 == Dom (ArgInfo h2 m2 _ _) b2 s2 _ x2 =
    (h1, m1, b1, s1, x1) == (h2, m2, b2, s2, x2)

instance LensNamed NamedName (Dom' t e) where
  lensNamed f dom = f (domName dom) <&> \ nm -> dom { domName = nm }

instance LensArgInfo (Dom' t e) where
  getArgInfo        = domInfo
  setArgInfo ai dom = dom { domInfo = ai }
  mapArgInfo f  dom = dom { domInfo = f $ domInfo dom }

-- The other lenses are defined through LensArgInfo

instance LensHiding        (Dom' t e) where
instance LensModality      (Dom' t e) where
instance LensOrigin        (Dom' t e) where
instance LensFreeVariables (Dom' t e) where

-- Since we have LensModality, we get relevance and quantity by default

instance LensRelevance (Dom' t e) where
instance LensQuantity  (Dom' t e) where
instance LensCohesion  (Dom' t e) where

argFromDom :: Dom' t a -> Arg a
argFromDom Dom{domInfo = i, unDom = a} = Arg i a

namedArgFromDom :: Dom' t a -> NamedArg a
namedArgFromDom Dom{domInfo = i, domName = s, unDom = a} = Arg i $ Named s a

-- The following functions are less general than they could be:
-- @Dom@ could be replaced by @Dom' t@.
-- However, this causes problems with instance resolution in several places.
-- often for class AddContext.

domFromArg :: Arg a -> Dom a
domFromArg (Arg i a) = Dom i False Nothing Nothing a

domFromNamedArg :: NamedArg a -> Dom a
domFromNamedArg (Arg i a) = Dom i False (nameOf a) Nothing (namedThing a)

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

-- | Store the names of the record fields in the constructor.
--   This allows reduction of projection redexes outside of TCM.
--   For instance, during substitution and application.
data ConHead = ConHead
  { conName      :: QName     -- ^ The name of the constructor.
  , conInductive :: Induction -- ^ Record constructors can be coinductive.
  , conFields    :: [Arg QName]   -- ^ The name of the record fields.
      --   Empty list for data constructors.
      --   'Arg' is stored since the info in the constructor args
      --   might not be accurate because of subtyping (issue #2170).
  } deriving (Data, Show)

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

class LensConName a where
  getConName :: a -> QName
  setConName :: QName -> a -> a
  setConName = mapConName . const
  mapConName :: (QName -> QName) -> a -> a
  mapConName f a = setConName (f (getConName a)) a

instance LensConName ConHead where
  getConName = conName
  setConName c con = con { conName = c }

-- | Literals in internal syntax can include quoted terms.
type ILiteral = Literal' QuotedTerm

-- | Raw values.
--
--   @Def@ is used for both defined and undefined constants.
--   Assume there is a type declaration and a definition for
--     every constant, even if the definition is an empty
--     list of clauses.
--
data Term = Var {-# UNPACK #-} !Int Elims -- ^ @x es@ neutral
          | Lam ArgInfo (Abs Term)        -- ^ Terms are beta normal. Relevance is ignored
          | Lit ILiteral
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
            --   apply a dummy term to more of them.
  deriving (Data, Show)

data QuotedTerm = QuotedTerm
  { quotedType       :: Type
  , quotedTerm       :: Term
  , quotedCheckpoint :: CheckpointId
  } deriving (Data, Show)

type ConInfo = ConOrigin

-- | Eliminations, subsuming applications and projections.
--
data Elim' a
  = Apply (Arg a)         -- ^ Application.
  | Proj ProjOrigin QName -- ^ Projection.  'QName' is name of a record projection.
  | IApply a a a -- ^ IApply x y r, x and y are the endpoints
  deriving (Data, Show, Functor, Foldable, Traversable)

type Elim = Elim' Term
type Elims = [Elim]  -- ^ eliminations ordered left-to-right.

-- | This instance cheats on 'Proj', use with care.
--   'Proj's are always assumed to be 'UserWritten', since they have no 'ArgInfo'.
--   Same for IApply
instance LensOrigin (Elim' a) where
  getOrigin (Apply a)   = getOrigin a
  getOrigin Proj{}      = UserWritten
  getOrigin IApply{}    = UserWritten
  mapOrigin f (Apply a) = Apply $ mapOrigin f a
  mapOrigin f e@Proj{}  = e
  mapOrigin f e@IApply{} = e

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
  deriving (Data, Functor, Foldable, Traversable)

instance Decoration Abs where
  traverseF f (Abs   x a) = Abs   x <$> f a
  traverseF f (NoAbs x a) = NoAbs x <$> f a

-- | Types are terms with a sort annotation.
--
data Type'' t a = El { _getSort :: Sort' t, unEl :: a }
  deriving (Data, Show, Functor, Foldable, Traversable)

type Type' a = Type'' Term a

type Type = Type' Term

instance Decoration (Type'' t) where
  traverseF f (El s a) = El s <$> f a

class LensSort a where
  lensSort ::  Lens' Sort a
  getSort  :: a -> Sort
  getSort a = a ^. lensSort

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
  deriving (Data, Show, Functor, Foldable, Traversable)

type Telescope = Tele (Dom Type)

-- | Sorts.
--
data Sort' t
  = Type (Level' t)  -- ^ @Set ℓ@.
  | Prop (Level' t)  -- ^ @Prop ℓ@.
  | Inf         -- ^ @Setω@.
  | SizeUniv    -- ^ @SizeUniv@, a sort inhabited by type @Size@.
  | PiSort (Dom' t (Type'' t t)) (Abs (Sort' t)) -- ^ Sort of the pi type.
  | UnivSort (Sort' t) -- ^ Sort of another sort.
  | MetaS {-# UNPACK #-} !MetaId [Elim' t]
  | DefS QName [Elim' t] -- ^ A postulated sort.
  | DummyS String
    -- ^ A (part of a) term or type which is only used for internal purposes.
    --   Replaces the abuse of @Prop@ for a dummy sort.
    --   The @String@ typically describes the location where we create this dummy,
    --   but can contain other information as well.
  deriving (Data, Show)

type Sort = Sort' Term

-- | A level is a maximum expression of 0..n 'PlusLevel' expressions
--   each of which is a number or an atom plus a number.
--
--   The empty maximum is the canonical representation for level 0.
newtype Level' t = Max [PlusLevel' t]
  deriving (Show, Data)

type Level = Level' Term

data PlusLevel' t
  = ClosedLevel Integer     -- ^ @n@, to represent @Setₙ@.
  | Plus Integer (LevelAtom' t)  -- ^ @n + ℓ@.
  deriving (Show, Data)

type PlusLevel = PlusLevel' Term

-- | An atomic term of type @Level@.
data LevelAtom' t
  = MetaLevel MetaId [Elim' t]
    -- ^ A meta variable targeting @Level@ under some eliminations.
  | BlockedLevel MetaId t
    -- ^ A term of type @Level@ whose reduction is blocked by a meta.
  | NeutralLevel NotBlocked t
    -- ^ A neutral term of type @Level@.
  | UnreducedLevel t
    -- ^ Introduced by 'instantiate', removed by 'reduce'.
  deriving (Show, Data)

type LevelAtom = LevelAtom' Term

---------------------------------------------------------------------------
-- * Brave Terms
---------------------------------------------------------------------------

-- | Newtypes for terms that produce a dummy, rather than crash, when
--   applied to incompatible eliminations.
newtype BraveTerm = BraveTerm { unBrave :: Term } deriving (Data, Show)

---------------------------------------------------------------------------
-- * Blocked Terms
---------------------------------------------------------------------------

-- | Even if we are not stuck on a meta during reduction
--   we can fail to reduce a definition by pattern matching
--   for another reason.
data NotBlocked
  = StuckOn Elim
    -- ^ The 'Elim' is neutral and blocks a pattern match.
  | Underapplied
    -- ^ Not enough arguments were supplied to complete the matching.
  | AbsurdMatch
    -- ^ We matched an absurd clause, results in a neutral 'Def'.
  | MissingClauses
    -- ^ We ran out of clauses, all considered clauses
    --   produced an actual mismatch.
    --   This can happen when try to reduce a function application
    --   but we are still missing some function clauses.
    --   See "Agda.TypeChecking.Patterns.Match".
  | ReallyNotBlocked
    -- ^ Reduction was not blocked, we reached a whnf
    --   which can be anything but a stuck @'Def'@.
  deriving (Show, Data)

-- | 'ReallyNotBlocked' is the unit.
--   'MissingClauses' is dominant.
--   @'StuckOn'{}@ should be propagated, if tied, we take the left.
instance Semigroup NotBlocked where
  ReallyNotBlocked <> b = b
  -- MissingClauses is dominant (absorptive)
  b@MissingClauses <> _ = b
  _ <> b@MissingClauses = b
  -- StuckOn is second strongest
  b@StuckOn{}      <> _ = b
  _ <> b@StuckOn{}      = b
  b <> _                = b

instance Monoid NotBlocked where
  -- ReallyNotBlocked is neutral
  mempty  = ReallyNotBlocked
  mappend = (<>)

-- | Something where a meta variable may block reduction.
data Blocked t
  = Blocked    { theBlockingMeta :: MetaId    , ignoreBlocking :: t }
  | NotBlocked { blockingStatus  :: NotBlocked, ignoreBlocking :: t }
  deriving (Show, Functor, Foldable, Traversable)
  -- deriving (Eq, Ord, Functor, Foldable, Traversable)

-- | Blocking by a meta is dominant.
instance Applicative Blocked where
  pure = notBlocked
  f <*> e = ((f $> ()) `mappend` (e $> ())) $> ignoreBlocking f (ignoreBlocking e)

-- -- | Blocking by a meta is dominant.
-- instance Applicative Blocked where
--   pure = notBlocked
--   Blocked x f     <*> e                = Blocked x $ f (ignoreBlocking e)
--   NotBlocked nb f <*> Blocked    x   e = Blocked x $ f e
--   NotBlocked nb f <*> NotBlocked nb' e = NotBlocked (nb `mappend` nb') $ f e

-- | @'Blocked' t@ without the @t@.
type Blocked_ = Blocked ()

instance Semigroup Blocked_ where
  b@Blocked{}    <> _              = b
  _              <> b@Blocked{}    = b
  NotBlocked x _ <> NotBlocked y _ = NotBlocked (x <> y) ()

instance Monoid Blocked_ where
  mempty = notBlocked ()
  mappend = (<>)

-- | When trying to reduce @f es@, on match failed on one
--   elimination @e ∈ es@ that came with info @r :: NotBlocked@.
--   @stuckOn e r@ produces the new @NotBlocked@ info.
--
--   'MissingClauses' must be propagated, as this is blockage
--   that can be lifted in the future (as more clauses are added).
--
--   @'StuckOn' e0@ is also propagated, since it provides more
--   precise information as @StuckOn e@ (as @e0@ is the original
--   reason why reduction got stuck and usually a subterm of @e@).
--   An information like @StuckOn (Apply (Arg info (Var i [])))@
--   (stuck on a variable) could be used by the lhs/coverage checker
--   to trigger a split on that (pattern) variable.
--
--   In the remaining cases for @r@, we are terminally stuck
--   due to @StuckOn e@.  Propagating @'AbsurdMatch'@ does not
--   seem useful.
--
--   'Underapplied' must not be propagated, as this would mean
--   that @f es@ is underapplied, which is not the case (it is stuck).
--   Note that 'Underapplied' can only arise when projection patterns were
--   missing to complete the original match (in @e@).
--   (Missing ordinary pattern would mean the @e@ is of function type,
--   but we cannot match against something of function type.)
stuckOn :: Elim -> NotBlocked -> NotBlocked
stuckOn e r =
  case r of
    MissingClauses   -> r
    StuckOn{}        -> r
    Underapplied     -> r'
    AbsurdMatch      -> r'
    ReallyNotBlocked -> r'
  where r' = StuckOn e

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
    { clauseLHSRange  :: Range
    , clauseFullRange :: Range
    , clauseTel       :: Telescope
      -- ^ @Δ@: The types of the pattern variables in dependency order.
    , namedClausePats :: NAPs
      -- ^ @Δ ⊢ ps@.  The de Bruijn indices refer to @Δ@.
    , clauseBody      :: Maybe Term
      -- ^ @Just v@ with @Δ ⊢ v@ for a regular clause, or @Nothing@ for an
      --   absurd one.
    , clauseType      :: Maybe (Arg Type)
      -- ^ @Δ ⊢ t@.  The type of the rhs under @clauseTel@.
      --   Used, e.g., by @TermCheck@.
      --   Can be 'Irrelevant' if we encountered an irrelevant projection
      --   pattern on the lhs.
    , clauseCatchall  :: Bool
      -- ^ Clause has been labelled as CATCHALL.
    , clauseUnreachable :: Maybe Bool
      -- ^ Clause has been labelled as unreachable by the coverage checker.
      --   @Nothing@ means coverage checker has not run yet (clause may be unreachable).
      --   @Just False@ means clause is not unreachable.
      --   @Just True@ means clause is unreachable.
    }
  deriving (Data, Show)

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
  deriving (Data, Show, Eq)

-- | Patterns are variables, constructors, or wildcards.
--   @QName@ is used in @ConP@ rather than @Name@ since
--     a constructor might come from a particular namespace.
--     This also meshes well with the fact that values (i.e.
--     the arguments we are matching with) use @QName@.
--
data Pattern' x
  = VarP PatOrigin x
    -- ^ @x@
  | DotP PatOrigin Term
    -- ^ @.t@
  | ConP ConHead ConPatternInfo [NamedArg (Pattern' x)]
    -- ^ @c ps@
    --   The subpatterns do not contain any projection copatterns.
  | LitP Literal
    -- ^ E.g. @5@, @"hello"@.
  | ProjP ProjOrigin QName
    -- ^ Projection copattern.  Can only appear by itself.
  | IApplyP PatOrigin Term Term x
    -- ^ Path elimination pattern, like @VarP@ but keeps track of endpoints.
  | DefP PatOrigin QName [NamedArg (Pattern' x)]
    -- ^ Used for HITs, the QName should be the one from primHComp.
  deriving (Data, Show, Functor, Foldable, Traversable)

type Pattern = Pattern' PatVarName
    -- ^ The @PatVarName@ is a name suggestion.

varP :: a -> Pattern' a
varP = VarP PatOSystem

dotP :: Term -> Pattern' a
dotP = DotP PatOSystem

-- | Type used when numbering pattern variables.
data DBPatVar = DBPatVar
  { dbPatVarName  :: PatVarName
  , dbPatVarIndex :: Int
  } deriving (Data, Show, Eq)

type DeBruijnPattern = Pattern' DBPatVar

namedVarP :: PatVarName -> Named_ Pattern
namedVarP x = Named named $ varP x
  where named = if isUnderscore x then Nothing else Just $ WithOrigin Inserted $ unranged x

namedDBVarP :: Int -> PatVarName -> Named_ DeBruijnPattern
namedDBVarP m = (fmap . fmap) (\x -> DBPatVar x m) . namedVarP

-- | Make an absurd pattern with the given de Bruijn index.
absurdP :: Int -> DeBruijnPattern
absurdP = VarP PatOAbsurd . DBPatVar absurdPatternName

-- | The @ConPatternInfo@ states whether the constructor belongs to
--   a record type (@Just@) or data type (@Nothing@).
--   In the former case, the @PatOrigin@ says whether the record pattern
--   orginates from the expansion of an implicit pattern.
--   The @Type@ is the type of the whole record pattern.
--   The scope used for the type is given by any outer scope
--   plus the clause's telescope ('clauseTel').
data ConPatternInfo = ConPatternInfo
  { conPRecord :: Maybe PatOrigin
    -- ^ @Nothing@ if data constructor.
    --   @Just@ if record constructor.
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
    -- ^ Lazy patterns are generated by the forcing translation
    --   ('Agda.TypeChecking.Forcing.forcingTranslation') and are dropped by
    --   the clause compiler (TODO: not yet)
    --   ('Agda.TypeChecking.CompiledClause.Compile.compileClauses') when the
    --   variables they bind are unused. The GHC backend compiles lazy matches
    --   to lazy patterns in Haskell (TODO: not yet).
  }
  deriving (Data, Show)

noConPatternInfo :: ConPatternInfo
noConPatternInfo = ConPatternInfo Nothing False Nothing False

-- | Build partial 'ConPatternInfo' from 'ConInfo'
toConPatternInfo :: ConInfo -> ConPatternInfo
toConPatternInfo ConORec = noConPatternInfo{ conPRecord = Just PatORec }
toConPatternInfo _ = noConPatternInfo

-- | Build 'ConInfo' from 'ConPatternInfo'.
fromConPatternInfo :: ConPatternInfo -> ConInfo
fromConPatternInfo = maybe ConOCon patToConO . conPRecord
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
      PatOLit    -> __IMPOSSIBLE__
      PatOAbsurd -> ConOSystem

-- | Extract pattern variables in left-to-right order.
--   A 'DotP' is also treated as variable (see docu for 'Clause').
class PatternVars a b | b -> a where
  patternVars :: b -> [Arg (Either a Term)]

instance PatternVars a (Arg (Pattern' a)) where
  -- patternVars :: Arg (Pattern' a) -> [Arg (Either a Term)]
  patternVars (Arg i (VarP _ x)   ) = [Arg i $ Left x]
  patternVars (Arg i (DotP _ t)   ) = [Arg i $ Right t]
  patternVars (Arg _ (ConP _ _ ps)) = patternVars ps
  patternVars (Arg _ (DefP _ _ ps)) = patternVars ps
  patternVars (Arg _ (LitP _)     ) = []
  patternVars (Arg _ ProjP{}      ) = []
  patternVars (Arg i (IApplyP _ _ _ x)) = [Arg i $ Left x]


instance PatternVars a (NamedArg (Pattern' a)) where
  patternVars = patternVars . fmap namedThing

instance PatternVars a b => PatternVars a [b] where
  patternVars = concatMap patternVars


-- | Retrieve the origin of a pattern
patternOrigin :: Pattern' x -> Maybe PatOrigin
patternOrigin (VarP o _) = Just o
patternOrigin (DotP o _) = Just o
patternOrigin LitP{}     = Nothing
patternOrigin (ConP _ ci _) = conPRecord ci
patternOrigin ProjP{}    = Nothing
patternOrigin (IApplyP o _ _ _) = Just o
patternOrigin (DefP o _ _) = Just o

-- | Does the pattern perform a match that could fail?
properlyMatching :: DeBruijnPattern -> Bool
properlyMatching p
  | patternOrigin p == Just PatOAbsurd = True
properlyMatching VarP{} = False
properlyMatching DotP{} = False
properlyMatching LitP{} = True
properlyMatching (ConP _ ci ps) = isNothing (conPRecord ci) || -- not a record cons
  List.any (properlyMatching . namedArg) ps  -- or one of subpatterns is a proper m
properlyMatching ProjP{} = True
properlyMatching IApplyP{} = False
properlyMatching DefP{}  = True

instance IsProjP (Pattern' a) where
  isProjP (ProjP o d) = Just (o, unambiguous d)
  isProjP _ = Nothing

-----------------------------------------------------------------------------
-- * Explicit substitutions
-----------------------------------------------------------------------------

-- | Substitutions.

data Substitution' a

  = IdS
    -- ^ Identity substitution.
    --   @Γ ⊢ IdS : Γ@

  | EmptyS Empty
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

  | Strengthen Empty (Substitution' a)
    -- ^ Strengthening substitution.  First argument is @__IMPOSSIBLE__@.
    --   Apply this to a term which does not contain variable 0
    --   to lower all de Bruijn indices by one.
    --   @
    --             Γ ⊢ ρ : Δ
    --     ---------------------------
    --     Γ ⊢ Strengthen ρ : Δ, A
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
           , Data
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
  = EqualityType
    { eqtSort  :: Sort     -- ^ Sort of this type.
    , eqtName  :: QName    -- ^ Builtin EQUALITY.
    , eqtParams :: [Arg Term] -- ^ Hidden.  Empty or @Level@.
    , eqtType  :: Arg Term -- ^ Hidden
    , eqtLhs   :: Arg Term -- ^ NotHidden
    , eqtRhs   :: Arg Term -- ^ NotHidden
    }
  | OtherType Type -- ^ reduced

isEqualityType :: EqualityView -> Bool
isEqualityType EqualityType{} = True
isEqualityType OtherType{}    = False

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

-- | Aux: A dummy term to constitute a dummy term/level/sort/type.
dummyTerm' :: String -> Int -> Term
dummyTerm' file line = flip Dummy [] $ file ++ ":" ++ show line

-- | Aux: A dummy level to constitute a level/sort.
dummyLevel' :: String -> Int -> Level
dummyLevel' file line = unreducedLevel $ dummyTerm' file line

-- | A dummy term created at location.
--   Note: use macro __DUMMY_TERM__ !
dummyTerm :: String -> Int -> Term
dummyTerm file = dummyTerm' ("dummyTerm: " ++ file)

__DUMMY_TERM__ :: HasCallStack => Term
__DUMMY_TERM__ = withFileAndLine' (freezeCallStack callStack) dummyTerm

-- | A dummy level created at location.
--   Note: use macro __DUMMY_LEVEL__ !
dummyLevel :: String -> Int -> Level
dummyLevel file = dummyLevel' ("dummyLevel: " ++ file)

__DUMMY_LEVEL__ :: HasCallStack => Level
__DUMMY_LEVEL__ = withFileAndLine' (freezeCallStack callStack) dummyLevel

-- | A dummy sort created at location.
--   Note: use macro __DUMMY_SORT__ !
dummySort :: String -> Int -> Sort
dummySort file line = DummyS $ file ++ ":" ++ show line

__DUMMY_SORT__ :: HasCallStack => Sort
__DUMMY_SORT__ = withFileAndLine' (freezeCallStack callStack) dummySort

-- | A dummy type created at location.
--   Note: use macro __DUMMY_TYPE__ !
dummyType :: String -> Int -> Type
dummyType file line = El (DummyS "") $ dummyTerm' ("dummyType: " ++ file) line

__DUMMY_TYPE__ :: HasCallStack => Type
__DUMMY_TYPE__ = withFileAndLine' (freezeCallStack callStack) dummyType

-- | Context entries without a type have this dummy type.
--   Note: use macro __DUMMY_DOM__ !
dummyDom :: String -> Int -> Dom Type
dummyDom file line = defaultDom $ dummyType file line

__DUMMY_DOM__ :: HasCallStack => Dom Type
__DUMMY_DOM__ = withFileAndLine' (freezeCallStack callStack) dummyDom

unreducedLevel :: Term -> Level
unreducedLevel v = Max [ Plus 0 $ UnreducedLevel v ]

-- | Top sort (Set\omega).
topSort :: Type
topSort = sort Inf

sort :: Sort -> Type
sort s = El (UnivSort s) $ Sort s

varSort :: Int -> Sort
varSort n = Type $ Max [Plus 0 $ NeutralLevel mempty $ var n]

tmSort :: Term -> Sort
tmSort t = Type $ Max [Plus 0 $ UnreducedLevel t]

levelSuc :: Level -> Level
levelSuc (Max []) = Max [ClosedLevel 1]
levelSuc (Max as) = Max $ map inc as
  where inc (ClosedLevel n) = ClosedLevel (n + 1)
        inc (Plus n l)      = Plus (n + 1) l

mkType :: Integer -> Sort
mkType n = Type $ Max [ClosedLevel n | n > 0]

mkProp :: Integer -> Sort
mkProp n = Prop $ Max [ClosedLevel n | n > 0]

isSort :: Term -> Maybe Sort
isSort v = case v of
  Sort s -> Just s
  _      -> Nothing

impossibleTerm :: String -> Int -> Term
impossibleTerm file line = flip Dummy [] $ unlines
  [ "An internal error has occurred. Please report this as a bug."
  , "Location of the error: " ++ file ++ ":" ++ show line
  ]

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
listTel :: Lens' ListTel Telescope
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
-- * Handling blocked terms.
---------------------------------------------------------------------------

blockingMeta :: Blocked t -> Maybe MetaId
blockingMeta (Blocked m _) = Just m
blockingMeta NotBlocked{}  = Nothing

blocked :: MetaId -> a -> Blocked a
blocked = Blocked

notBlocked :: a -> Blocked a
notBlocked = NotBlocked ReallyNotBlocked

blocked_ :: MetaId -> Blocked_
blocked_ x = blocked x ()

notBlocked_ :: Blocked_
notBlocked_ = notBlocked ()

---------------------------------------------------------------------------
-- * Simple operations on terms and types.
---------------------------------------------------------------------------

-- | Removing a topmost 'DontCare' constructor.
stripDontCare :: Term -> Term
stripDontCare v = case v of
  DontCare v -> v
  _          -> v

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
unSpine = unSpine' $ const True

-- | Convert 'Proj' projection eliminations
--   according to their 'ProjOrigin' into
--   'Def' projection applications.
unSpine' :: (ProjOrigin -> Bool) -> Term -> Term
unSpine' p v =
  case hasElims v of
    Just (h, es) -> loop h [] es
    Nothing      -> v
  where
    loop :: (Elims -> Term) -> Elims -> Elims -> Term
    loop h res es =
      case es of
        []                   -> v
        Proj o f : es' | p o -> loop (Def f) [Apply (defaultArg v)] es'
        e        : es'       -> loop h (e : res) es'
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
    -- Andreas, 2016-04-13, Issue 1932: We convert λ x → x .f  into f
    Lam _ (Abs _ v)  -> case v of
      Var 0 [Proj _o f] -> Just (Def f, [])
      _ -> Nothing
    Lam{}      -> Nothing
    Pi{}       -> Nothing
    Sort{}     -> Nothing
    Level{}    -> Nothing
    DontCare{} -> Nothing
    Dummy{}    -> Nothing

-- | Drop 'Apply' constructor. (Safe)
isApplyElim :: Elim' a -> Maybe (Arg a)
isApplyElim (Apply u) = Just u
isApplyElim Proj{}    = Nothing
isApplyElim (IApply _ _ r) = Just (defaultArg r)

isApplyElim' :: Empty -> Elim' a -> Arg a
isApplyElim' e = fromMaybe (absurd e) . isApplyElim

-- | Drop 'Apply' constructors. (Safe)
allApplyElims :: [Elim' a] -> Maybe [Arg a]
allApplyElims = mapM isApplyElim

-- | Split at first non-'Apply'
splitApplyElims :: [Elim' a] -> ([Arg a], [Elim' a])
splitApplyElims (Apply u : es) = mapFst (u :) $ splitApplyElims es
splitApplyElims es             = ([], es)

class IsProjElim e where
  isProjElim  :: e -> Maybe (ProjOrigin, QName)

instance IsProjElim (Elim' a) where
  isProjElim (Proj o d) = Just (o, d)
  isProjElim Apply{}    = Nothing
  isProjElim IApply{} = Nothing

-- | Discards @Proj f@ entries.
argsFromElims :: Elims -> Args
argsFromElims = mapMaybe isApplyElim

-- | Drop 'Proj' constructors. (Safe)
allProjElims :: Elims -> Maybe [(ProjOrigin, QName)]
allProjElims = mapM isProjElim

---------------------------------------------------------------------------
-- * Checkpoint ids
---------------------------------------------------------------------------

newtype CheckpointId = CheckpointId Int
  deriving (Data, Eq, Ord, Enum, Real, Integral, Num)

instance Show CheckpointId where
  show (CheckpointId n) = show n

instance Pretty CheckpointId where
  pretty (CheckpointId n) = pretty n

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
  empty = Clause empty empty empty empty empty empty False Nothing
  null (Clause _ _ tel pats body _ _ _)
    =  null tel
    && null pats
    && null body


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

instance Sized a => Sized (Abs a) where
  size = size . unAbs

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
  tsize v = case v of
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
  tsize s = case s of
    Type l    -> 1 + tsize l
    Prop l    -> 1 + tsize l
    Inf       -> 1
    SizeUniv  -> 1
    PiSort a s -> 1 + tsize a + tsize s
    UnivSort s -> 1 + tsize s
    MetaS _ es -> 1 + tsize es
    DefS _ es  -> 1 + tsize es
    DummyS{}   -> 1

instance TermSize Level where
  tsize (Max as) = 1 + tsize as

instance TermSize PlusLevel where
  tsize (ClosedLevel _) = 1
  tsize (Plus _ a)      = tsize a

instance TermSize LevelAtom where
  tsize (MetaLevel _   vs) = 1 + tsize vs
  tsize (BlockedLevel _ v) = tsize v
  tsize (NeutralLevel _ v) = tsize v
  tsize (UnreducedLevel v) = tsize v

instance TermSize a => TermSize (Substitution' a) where
  tsize IdS                = 1
  tsize (EmptyS _)         = 1
  tsize (Wk _ rho)         = 1 + tsize rho
  tsize (t :# rho)         = 1 + tsize t + tsize rho
  tsize (Strengthen _ rho) = 1 + tsize rho
  tsize (Lift _ rho)       = 1 + tsize rho

---------------------------------------------------------------------------
-- * KillRange instances.
---------------------------------------------------------------------------

instance KillRange ConHead where
  killRange (ConHead c i fs) = killRange3 ConHead c i fs

instance KillRange Term where
  killRange v = case v of
    Var i vs    -> killRange1 (Var i) vs
    Def c vs    -> killRange2 Def c vs
    Con c ci vs -> killRange3 Con c ci vs
    MetaV m vs  -> killRange1 (MetaV m) vs
    Lam i f     -> killRange2 Lam i f
    Lit l       -> killRange1 Lit l
    Level l     -> killRange1 Level l
    Pi a b      -> killRange2 Pi a b
    Sort s      -> killRange1 Sort s
    DontCare mv -> killRange1 DontCare mv
    Dummy{}     -> v

instance KillRange Level where
  killRange (Max as) = killRange1 Max as

instance KillRange PlusLevel where
  killRange l@ClosedLevel{} = l
  killRange (Plus n l) = killRange1 (Plus n) l

instance KillRange LevelAtom where
  killRange (MetaLevel n as)   = killRange1 (MetaLevel n) as
  killRange (BlockedLevel m v) = killRange1 (BlockedLevel m) v
  killRange (NeutralLevel r v) = killRange1 (NeutralLevel r) v
  killRange (UnreducedLevel v) = killRange1 UnreducedLevel v

instance (KillRange a) => KillRange (Type' a) where
  killRange (El s v) = killRange2 El s v

instance KillRange Sort where
  killRange s = case s of
    Inf        -> Inf
    SizeUniv   -> SizeUniv
    Type a     -> killRange1 Type a
    Prop a     -> killRange1 Prop a
    PiSort a s -> killRange2 PiSort a s
    UnivSort s -> killRange1 UnivSort s
    MetaS x es -> killRange1 (MetaS x) es
    DefS d es  -> killRange2 DefS d es
    DummyS{}   -> s

instance KillRange Substitution where
  killRange IdS                  = IdS
  killRange (EmptyS err)         = EmptyS err
  killRange (Wk n rho)           = killRange1 (Wk n) rho
  killRange (t :# rho)           = killRange2 (:#) t rho
  killRange (Strengthen err rho) = killRange1 (Strengthen err) rho
  killRange (Lift n rho)         = killRange1 (Lift n) rho

instance KillRange PatOrigin where
  killRange = id

instance KillRange ConPatternInfo where
  killRange (ConPatternInfo mr b mt lz) = killRange1 (ConPatternInfo mr b) mt lz

instance KillRange DBPatVar where
  killRange (DBPatVar x i) = killRange2 DBPatVar x i

instance KillRange a => KillRange (Pattern' a) where
  killRange p =
    case p of
      VarP o x         -> killRange2 VarP o x
      DotP o v         -> killRange2 DotP o v
      ConP con info ps -> killRange3 ConP con info ps
      LitP l           -> killRange1 LitP l
      ProjP o q        -> killRange1 (ProjP o) q
      IApplyP o u t x  -> killRange3 (IApplyP o) u t x
      DefP o q ps      -> killRange2 (DefP o) q ps

instance KillRange Clause where
  killRange (Clause rl rf tel ps body t catchall unreachable) =
    killRange8 Clause rl rf tel ps body t catchall unreachable

instance KillRange a => KillRange (Tele a) where
  killRange = fmap killRange

instance KillRange a => KillRange (Blocked a) where
  killRange = fmap killRange

instance KillRange a => KillRange (Abs a) where
  killRange = fmap killRange

instance KillRange a => KillRange (Elim' a) where
  killRange = fmap killRange

---------------------------------------------------------------------------
-- * UniverseBi instances.
---------------------------------------------------------------------------

instanceUniverseBiT' [] [t| (([Type], [Clause]), Pattern) |]
instanceUniverseBiT' [] [t| (Args, Pattern)               |]
instanceUniverseBiT' [] [t| (Elims, Pattern)              |] -- ?
instanceUniverseBiT' [] [t| (([Type], [Clause]), Term)    |]
instanceUniverseBiT' [] [t| (Args, Term)                  |]
instanceUniverseBiT' [] [t| (Elims, Term)                 |] -- ?
instanceUniverseBiT' [] [t| ([Term], Term)                |]

-----------------------------------------------------------------------------
-- * Simple pretty printing
-----------------------------------------------------------------------------

instance Pretty a => Pretty (Substitution' a) where
  prettyPrec = pr
    where
    pr p rho = case rho of
      IdS              -> "idS"
      EmptyS err       -> "emptyS"
      t :# rho         -> mparens (p > 2) $ sep [ pr 2 rho <> ",", prettyPrec 3 t ]
      Strengthen _ rho -> mparens (p > 9) $ "strS" <+> pr 10 rho
      Wk n rho         -> mparens (p > 9) $ text ("wkS " ++ show n) <+> pr 10 rho
      Lift n rho       -> mparens (p > 9) $ text ("liftS " ++ show n) <+> pr 10 rho

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
        sep [ prettyPrec 1 (unDom a) <+> "->"
            , nest 2 $ pretty b ]
      Pi a b               -> mparens (p > 0) $
        sep [ pDom (domInfo a) (text (absName b) <+> ":" <+> pretty (unDom a)) <+> "->"
            , nest 2 $ pretty (unAbs b) ]
      Sort s      -> prettyPrec p s
      Level l     -> prettyPrec p l
      MetaV x els -> pretty x `pApp` els
      DontCare v  -> prettyPrec p v
      Dummy s es  -> parens (text s) `pApp` es
    where
      pApp d els = mparens (not (null els) && p > 9) $
                   sep [d, nest 2 $ fsep (map (prettyPrec 10) els)]

instance Pretty QuotedTerm where
  prettyPrec p q = mparens (p > 9) $ sep ["quoteTerm", prettyPrec 10 $ quotedTerm q]

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

instance Pretty Level where
  prettyPrec p (Max as) =
    case as of
      []  -> prettyPrec p (ClosedLevel 0 :: PlusLevel)
      [a] -> prettyPrec p a
      _   -> mparens (p > 9) $ List.foldr1 (\a b -> "lub" <+> a <+> b) $ map (prettyPrec 10) as

instance Pretty PlusLevel where
  prettyPrec p l =
    case l of
      ClosedLevel n -> sucs p n $ const "lzero"
      Plus n a      -> sucs p n $ \p -> prettyPrec p a
    where
      sucs p 0 d = d p
      sucs p n d = mparens (p > 9) $ "lsuc" <+> sucs 10 (n - 1) d

instance Pretty LevelAtom where
  prettyPrec p a =
    case a of
      MetaLevel x els  -> prettyPrec p (MetaV x els)
      BlockedLevel _ v -> prettyPrec p v
      NeutralLevel _ v -> prettyPrec p v
      UnreducedLevel v -> prettyPrec p v

instance Pretty Sort where
  prettyPrec p s =
    case s of
      Type (Max []) -> "Set"
      Type (Max [ClosedLevel n]) -> text $ "Set" ++ show n
      Type l -> mparens (p > 9) $ "Set" <+> prettyPrec 10 l
      Prop (Max []) -> "Prop"
      Prop (Max [ClosedLevel n]) -> text $ "Prop" ++ show n
      Prop l -> mparens (p > 9) $ "Prop" <+> prettyPrec 10 l
      Inf -> "Setω"
      SizeUniv -> "SizeUniv"
      PiSort a b -> mparens (p > 9) $
        "piSort" <+> pDom (domInfo a) (text (absName b) <+> ":" <+> pretty (unDom a))
                      <+> parens (sep [ text ("λ " ++ absName b ++ " ->")
                                      , nest 2 $ pretty (unAbs b) ])
      UnivSort s -> mparens (p > 9) $ "univSort" <+> prettyPrec 10 s
      MetaS x es -> prettyPrec p $ MetaV x es
      DefS d es  -> prettyPrec p $ Def d es
      DummyS s   -> parens $ text s

instance Pretty Type where
  prettyPrec p (El _ a) = prettyPrec p a

instance Pretty tm => Pretty (Elim' tm) where
  prettyPrec p (Apply v)    = prettyPrec p v
  prettyPrec _ (Proj _o x)  = text ("." ++ prettyShow x)
  prettyPrec p (IApply x y r) = prettyPrec p r

instance Pretty DBPatVar where
  prettyPrec _ x = text $ patVarNameToString (dbPatVarName x) ++ "@" ++ show (dbPatVarIndex x)

instance Pretty a => Pretty (Pattern' a) where
  prettyPrec n (VarP _o x)   = prettyPrec n x
  prettyPrec _ (DotP _o t)   = "." <> prettyPrec 10 t
  prettyPrec n (ConP c i nps)= mparens (n > 0 && not (null nps)) $
    pretty (conName c) <+> fsep (map (prettyPrec 10) ps)
    where ps = map (fmap namedThing) nps
  prettyPrec n (DefP o q nps)= mparens (n > 0 && not (null nps)) $
    pretty q <+> fsep (map (prettyPrec 10) ps)
    where ps = map (fmap namedThing) nps
  -- -- Version with printing record type:
  -- prettyPrec _ (ConP c i ps) = (if b then braces else parens) $ prTy $
  --   text (show $ conName c) <+> fsep (map (pretty . namedArg) ps)
  --   where
  --     b = maybe False (== ConOSystem) $ conPRecord i
  --     prTy d = caseMaybe (conPType i) d $ \ t -> d  <+> ":" <+> pretty t
  prettyPrec _ (LitP l)      = pretty l
  prettyPrec _ (ProjP _o q)  = text ("." ++ prettyShow q)
  prettyPrec n (IApplyP _o _ _ x) = prettyPrec n x
-----------------------------------------------------------------------------
-- * NFData instances
-----------------------------------------------------------------------------

-- Note: only strict in the shape of the terms.

instance NFData Term where
  rnf v = case v of
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
  rnf s = case s of
    Type l   -> rnf l
    Prop l   -> rnf l
    Inf      -> ()
    SizeUniv -> ()
    PiSort a b -> rnf (a, unAbs b)
    UnivSort a -> rnf a
    MetaS _ es -> rnf es
    DefS _ es  -> rnf es
    DummyS _   -> ()

instance NFData Level where
  rnf (Max as) = rnf as

instance NFData PlusLevel where
  rnf (ClosedLevel n) = rnf n
  rnf (Plus n l) = rnf (n, l)

instance NFData LevelAtom where
  rnf (MetaLevel _ es)   = rnf es
  rnf (BlockedLevel _ v) = rnf v
  rnf (NeutralLevel _ v) = rnf v
  rnf (UnreducedLevel v) = rnf v

instance NFData a => NFData (Elim' a) where
  rnf (Apply x) = rnf x
  rnf Proj{}    = ()
  rnf (IApply x y r) = rnf x `seq` rnf y `seq` rnf r

instance NFData e => NFData (Dom e) where
  rnf (Dom a b c d e) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e

instance NFData CheckpointId where
  rnf (CheckpointId n) = rnf n

instance NFData QuotedTerm where
  rnf (QuotedTerm a b c) = rnf (a, b, c)
