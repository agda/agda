{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

module Agda.Syntax.Internal
    ( module Agda.Syntax.Internal
    , module Agda.Syntax.Abstract.Name
    , module Agda.Utils.Pointer
    , MetaId(..)
    ) where

import Prelude hiding (foldr, mapM, null)

import Control.Applicative hiding (empty)
import Control.Monad.Identity hiding (mapM)
import Control.DeepSeq

import Data.Foldable ( Foldable, foldMap )
import Data.Function
import qualified Data.List as List
import Data.Maybe
import Data.Semigroup (Semigroup, Monoid, (<>), mempty, mappend, Sum(..))

-- base-4.7 defines the Num instance for Sum
#if !(MIN_VERSION_base(4,7,0))
import Data.Orphans             ()
#endif

import Data.Traversable
import Data.Typeable (Typeable)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Concrete.Pretty (prettyHiding)
import Agda.Syntax.Abstract.Name

import Agda.Utils.Empty

-- See Issue 1593.
#if !MIN_VERSION_transformers(0,4,1)
import Agda.Utils.Except ( Error(noMsg) )
#endif

import Agda.Utils.Functor
import Agda.Utils.Geniplate
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pointer
import Agda.Utils.Size
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Pretty hiding ((<>))
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

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
  , conFields    :: [QName]   -- ^ The name of the record fields.
                              --   Empty list for data constructors.
                              --   'Arg' is not needed here since it
                              --   is stored in the constructor args.
  } deriving (Typeable)

instance Eq ConHead where
  (==) = (==) `on` conName

instance Ord ConHead where
  (<=) = (<=) `on` conName

instance Show ConHead where
  show (ConHead c i fs) = show c ++ "(" ++ show i ++ ")" ++ show fs

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
          | Con ConHead ConInfo Args      -- ^ @c vs@ or @record { fs = vs }@
          | Pi (Dom Type) (Abs Type)      -- ^ dependent or non-dependent function space
          | Sort Sort
          | Level Level
          | MetaV {-# UNPACK #-} !MetaId Elims
          | DontCare Term
            -- ^ Irrelevant stuff in relevant position, but created
            --   in an irrelevant context.  Basically, an internal
            --   version of the irrelevance axiom @.irrAx : .A -> A@.
          | Shared !(Ptr Term)
            -- ^ Explicit sharing
  deriving (Typeable, Show)

type ConInfo = ConOrigin

-- | Eliminations, subsuming applications and projections.
--
data Elim' a
  = Apply (Arg a)         -- ^ Application.
  | Proj ProjOrigin QName -- ^ Projection.  'QName' is name of a record projection.
  deriving (Typeable, Show, Functor, Foldable, Traversable)

type Elim = Elim' Term
type Elims = [Elim]  -- ^ eliminations ordered left-to-right.

-- | This instance cheats on 'Proj', use with care.
--   'Proj's are always assumed to be 'UserWritten', since they have no 'ArgInfo'.
instance LensOrigin (Elim' a) where
  getOrigin (Apply a)   = getOrigin a
  getOrigin Proj{}      = UserWritten
  mapOrigin f (Apply a) = Apply $ mapOrigin f a
  mapOrigin f e@Proj{}  = e

-- | Names in binders and arguments.
type ArgName = String

argNameToString :: ArgName -> String
argNameToString = id

stringToArgName :: String -> ArgName
stringToArgName = id

appendArgNames :: ArgName -> ArgName -> ArgName
appendArgNames = (++)

nameToArgName :: Name -> ArgName
nameToArgName = stringToArgName . prettyShow

-- | Binder.
--   'Abs': The bound variable might appear in the body.
--   'NoAbs' is pseudo-binder, it does not introduce a fresh variable,
--      similar to the @const@ of Haskell.
data Abs a = Abs   { absName :: ArgName, unAbs :: a }
               -- ^ The body has (at least) one free variable.
               --   Danger: 'unAbs' doesn't shift variables properly
           | NoAbs { absName :: ArgName, unAbs :: a }
  deriving (Typeable, Functor, Foldable, Traversable)

instance Decoration Abs where
  traverseF f (Abs   x a) = Abs   x <$> f a
  traverseF f (NoAbs x a) = NoAbs x <$> f a

-- | Types are terms with a sort annotation.
--
data Type' a = El { _getSort :: Sort, unEl :: a }
  deriving (Typeable, Show, Functor, Foldable, Traversable)

type Type = Type' Term

instance Decoration Type' where
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

instance LensSort a => LensSort (Abs a) where
  lensSort = traverseF . lensSort

-- | Sequence of types. An argument of the first type is bound in later types
--   and so on.
data Tele a = EmptyTel
            | ExtendTel a (Abs (Tele a))  -- ^ 'Abs' is never 'NoAbs'.
  deriving (Typeable, Show, Functor, Foldable, Traversable)

type Telescope = Tele (Dom Type)

-- | Sorts.
--
data Sort
  = Type Level  -- ^ @Set ℓ@.
  | Prop        -- ^ Dummy sort.
  | Inf         -- ^ @Setω@.
  | SizeUniv    -- ^ @SizeUniv@, a sort inhabited by type @Size@.
  | DLub Sort (Abs Sort)
    -- ^ Dependent least upper bound.
    --   If the free variable occurs in the second sort,
    --   the whole thing should reduce to Inf,
    --   otherwise it's the normal lub.
  deriving (Typeable, Show)

-- | A level is a maximum expression of 0..n 'PlusLevel' expressions
--   each of which is a number or an atom plus a number.
--
--   The empty maximum is the canonical representation for level 0.
newtype Level = Max [PlusLevel]
  deriving (Show, Typeable)

data PlusLevel
  = ClosedLevel Integer     -- ^ @n@, to represent @Setₙ@.
  | Plus Integer LevelAtom  -- ^ @n + ℓ@.
  deriving (Show, Typeable)

-- | An atomic term of type @Level@.
data LevelAtom
  = MetaLevel MetaId Elims
    -- ^ A meta variable targeting @Level@ under some eliminations.
  | BlockedLevel MetaId Term
    -- ^ A term of type @Level@ whose reduction is blocked by a meta.
  | NeutralLevel NotBlocked Term
    -- ^ A neutral term of type @Level@.
  | UnreducedLevel Term
    -- ^ Introduced by 'instantiate', removed by 'reduce'.
  deriving (Show, Typeable)

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
  deriving (Show, Typeable)

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
  mempty = ReallyNotBlocked
  mappend = (<>)

-- | Something where a meta variable may block reduction.
data Blocked t
  = Blocked    { theBlockingMeta :: MetaId    , ignoreBlocking :: t }
  | NotBlocked { blockingStatus  :: NotBlocked, ignoreBlocking :: t }
  deriving (Typeable, Show, Functor, Foldable, Traversable)
  -- deriving (Typeable, Eq, Ord, Functor, Foldable, Traversable)

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

-- See issues 1573 and 1674.
#if !MIN_VERSION_transformers(0,4,1)
instance Error Blocked_ where
  noMsg = mempty
#endif

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
    , namedClausePats :: [NamedArg DeBruijnPattern]
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
    }
  deriving (Typeable, Show)

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

-- | Patterns are variables, constructors, or wildcards.
--   @QName@ is used in @ConP@ rather than @Name@ since
--     a constructor might come from a particular namespace.
--     This also meshes well with the fact that values (i.e.
--     the arguments we are matching with) use @QName@.
--
data Pattern' x
  = VarP x
    -- ^ @x@
  | DotP Term
    -- ^ @.t@
  | ConP ConHead ConPatternInfo [NamedArg (Pattern' x)]
    -- ^ @c ps@
    --   The subpatterns do not contain any projection copatterns.
  | LitP Literal
    -- ^ E.g. @5@, @"hello"@.
  | ProjP ProjOrigin QName
    -- ^ Projection copattern.  Can only appear by itself.
  deriving (Typeable, Show, Functor, Foldable, Traversable)

type Pattern = Pattern' PatVarName
    -- ^ The @PatVarName@ is a name suggestion.

varP :: ArgName -> Pattern
varP = VarP

-- | Type used when numbering pattern variables.
data DBPatVar = DBPatVar
  { dbPatVarName  :: PatVarName
  , dbPatVarIndex :: Int
  } deriving (Typeable, Show)

type DeBruijnPattern = Pattern' DBPatVar

namedVarP :: PatVarName -> Named_ Pattern
namedVarP x = Named named $ varP x
  where named = if isUnderscore x then Nothing else Just $ unranged x

namedDBVarP :: Int -> PatVarName -> Named_ DeBruijnPattern
namedDBVarP m = (fmap . fmap) (\x -> DBPatVar x m) . namedVarP

-- | The @ConPatternInfo@ states whether the constructor belongs to
--   a record type (@Just@) or data type (@Nothing@).
--   In the former case, the @Bool@ says whether the record pattern
--   orginates from the expansion of an implicit pattern.
--   The @Type@ is the type of the whole record pattern.
--   The scope used for the type is given by any outer scope
--   plus the clause's telescope ('clauseTel').
data ConPatternInfo = ConPatternInfo
  { conPRecord :: Maybe ConOrigin
    -- ^ @Nothing@ if data constructor.
    --   @Just@ if record constructor.
  , conPType   :: Maybe (Arg Type)
    -- ^ The type of the whole constructor pattern.
    --   Should be present (@Just@) if constructor pattern is
    --   is generated ordinarily by type-checking.
    --   Could be absent (@Nothing@) if pattern comes from some
    --   plugin (like Agsy).
    --   Needed e.g. for with-clause stripping.
  }
  deriving (Typeable, Show)

noConPatternInfo :: ConPatternInfo
noConPatternInfo = ConPatternInfo Nothing Nothing

-- | Build partial 'ConPatternInfo' from 'ConInfo'
toConPatternInfo :: ConInfo -> ConPatternInfo
toConPatternInfo ConORec = ConPatternInfo (Just ConORec) Nothing
toConPatternInfo _ = noConPatternInfo

-- | Build 'ConInfo' from 'ConPatternInfo'.
fromConPatternInfo :: ConPatternInfo -> ConInfo
fromConPatternInfo = fromMaybe ConOSystem . conPRecord

-- | Extract pattern variables in left-to-right order.
--   A 'DotP' is also treated as variable (see docu for 'Clause').
patternVars :: Arg (Pattern' a) -> [Arg (Either a Term)]
patternVars (Arg i (VarP x)     ) = [Arg i $ Left x]
patternVars (Arg i (DotP t)     ) = [Arg i $ Right t]
patternVars (Arg i (ConP _ _ ps)) = List.concat $ map (patternVars . fmap namedThing) ps
patternVars (Arg i (LitP l)     ) = []
patternVars (Arg i ProjP{}      ) = []

-- | Does the pattern perform a match that could fail?
properlyMatching :: DeBruijnPattern -> Bool
properlyMatching (VarP x) = isAbsurdPatternName $ dbPatVarName x
properlyMatching DotP{} = False
properlyMatching LitP{} = True
properlyMatching (ConP _ ci ps) = isNothing (conPRecord ci) || -- not a record cons
  List.any (properlyMatching . namedArg) ps  -- or one of subpatterns is a proper m
properlyMatching ProjP{} = True

instance IsProjP (Pattern' a) where
  isProjP (ProjP o d) = Just (o, AmbQ [d])
  isProjP _ = Nothing

-----------------------------------------------------------------------------
-- * Explicit substitutions
-----------------------------------------------------------------------------

-- | Substitutions.

data Substitution' a

  = IdS
    -- ^ Identity substitution.
    --   @Γ ⊢ IdS : Γ@

  | EmptyS
    -- ^ Empty substitution, lifts from the empty context.
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
    -- ^ Weakning substitution, lifts to an extended context.
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

  deriving (Show, Functor, Foldable, Traversable)

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
-- * Pointers and Sharing
---------------------------------------------------------------------------

-- | Remove top-level @Shared@ data constructors.
ignoreSharing :: Term -> Term
ignoreSharing (Shared p) = ignoreSharing $ derefPtr p
ignoreSharing v          = v

ignoreSharingType :: Type -> Type
ignoreSharingType (El s v) = El s (ignoreSharing v)
-- ignoreSharingType v = v

-- | Introduce sharing.
shared_ :: Term -> Term
shared_ v@Shared{}   = v
shared_ v@(Var _ []) = v
shared_ v@(Con _ _ []) = v -- Issue 1691: sharing (zero : Nat) destroys constructorForm
shared_ v            = Shared (newPtr v)

-- | Typically m would be TCM and f would be Blocked.
updateSharedFM
#if __GLASGOW_HASKELL__ <= 708
  :: (Applicative m, Monad m, Traversable f)
#else
  :: (Monad m, Traversable f)
#endif
  => (Term -> m (f Term)) -> Term -> m (f Term)
updateSharedFM f v0@(Shared p) = do
  fv <- f (derefPtr p)
  flip traverse fv $ \v ->
    case derefPtr (setPtr v p) of
      Var _ [] -> return v
      _        -> return $! compressPointerChain v0
updateSharedFM f v = f v

updateSharedM :: Monad m => (Term -> m Term) -> Term -> m Term
updateSharedM f v0@(Shared p) = do
  v <- f (derefPtr p)
  case derefPtr (setPtr v p) of
    Var _ [] -> return v
    _        -> return $! compressPointerChain v0
updateSharedM f v = f v

updateShared :: (Term -> Term) -> Term -> Term
updateShared f v0@(Shared p) =
  case derefPtr (setPtr (f $ derefPtr p) p) of
    v@(Var _ []) -> v
    _            -> compressPointerChain v0
updateShared f v = f v

pointerChain :: Term -> [Ptr Term]
pointerChain (Shared p) = p : pointerChain (derefPtr p)
pointerChain _          = []

-- Redirect all top-level pointers to point to the last pointer. So, after
-- compression there are at most two top-level indirections. Then return the
-- inner-most pointer so we have only one pointer for the result.
compressPointerChain :: Term -> Term
compressPointerChain v =
  case reverse $ pointerChain v of
    p:_:ps@(_:_) -> setPointers (Shared p) ps
    p:_:_        -> (Shared p)
    _            -> v
  where
    setPointers u [] = u
    setPointers u (p : ps) =
      setPtr u p `seq` setPointers u ps

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
  case ignoreSharing v of
    DontCare{} -> v
    _          -> DontCare v

-- | A dummy type.
typeDontCare :: Type
typeDontCare = El Prop (Sort Prop)

-- | Top sort (Set\omega).
topSort :: Type
topSort = El Inf (Sort Inf)

sort :: Sort -> Type
sort s = El (sSuc s) $ Sort s

varSort :: Int -> Sort
varSort n = Type $ Max [Plus 0 $ NeutralLevel mempty $ var n]

-- | Get the next higher sort.
sSuc :: Sort -> Sort
sSuc Prop            = mkType 1
sSuc Inf             = Inf
sSuc SizeUniv        = SizeUniv
sSuc (DLub a b)      = DLub (sSuc a) (fmap sSuc b)
sSuc (Type l)        = Type $ levelSuc l

levelSuc :: Level -> Level
levelSuc (Max []) = Max [ClosedLevel 1]
levelSuc (Max as) = Max $ map inc as
  where inc (ClosedLevel n) = ClosedLevel (n + 1)
        inc (Plus n l)      = Plus (n + 1) l

mkType :: Integer -> Sort
mkType n = Type $ Max [ClosedLevel n | n > 0]

isSort :: Term -> Maybe Sort
isSort v = case ignoreSharing v of
  Sort s -> Just s
  _      -> Nothing

impossibleTerm :: String -> Int -> Term
impossibleTerm file line = Lit $ LitString noRange $ unlines
  [ "An internal error has occurred. Please report this as a bug."
  , "Location of the error: " ++ file ++ ":" ++ show line
  ]

hackReifyToMeta :: Term
hackReifyToMeta = DontCare $ Lit $ LitNat noRange (-42)

isHackReifyToMeta :: Term -> Bool
isHackReifyToMeta (DontCare (Lit (LitNat r (-42)))) = r == noRange
isHackReifyToMeta _ = False

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
    extTel (Dom info (x, a)) = ExtendTel (Dom info a) . Abs (f x)

-- | Convert a list telescope to a telescope.
telFromList :: ListTel -> Telescope
telFromList = telFromList' id

-- | Convert a telescope to its list form.
telToList :: Telescope -> ListTel
telToList EmptyTel                    = []
telToList (ExtendTel arg (Abs x tel)) = fmap (x,) arg : telToList tel
telToList (ExtendTel _    NoAbs{}   ) = __IMPOSSIBLE__

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
  sgTel (x, dom) = ExtendTel dom $ Abs x EmptyTel

instance SgTel (Dom (ArgName, Type)) where
  sgTel (Dom ai (x, t)) = ExtendTel (Dom ai t) $ Abs x EmptyTel

instance SgTel (Dom Type) where
  sgTel dom = sgTel (stringToArgName "_", dom)

---------------------------------------------------------------------------
-- * Handling blocked terms.
---------------------------------------------------------------------------

blockingMeta :: Blocked t -> Maybe MetaId
blockingMeta (Blocked m _) = Just m
blockingMeta NotBlocked{}  = Nothing

blocked :: MetaId -> a -> Blocked a
blocked x = Blocked x

notBlocked :: a -> Blocked a
notBlocked = NotBlocked ReallyNotBlocked

---------------------------------------------------------------------------
-- * Simple operations on terms and types.
---------------------------------------------------------------------------

-- | Removing a topmost 'DontCare' constructor.
stripDontCare :: Term -> Term
stripDontCare v = case ignoreSharing v of
  DontCare v -> v
  _          -> v

-- | Doesn't do any reduction.
arity :: Type -> Nat
arity t = case ignoreSharing $ unEl t of
  Pi  _ b -> 1 + arity (unAbs b)
  _       -> 0

-- | Make a name that is not in scope.
notInScopeName :: ArgName -> ArgName
notInScopeName = stringToArgName . ("." ++) . argNameToString

-- | Pick the better name suggestion, i.e., the one that is not just underscore.
class Suggest a b where
  suggest :: a -> b -> String

instance Suggest String String where
  suggest "_" y = y
  suggest  x  _ = x

instance Suggest (Abs a) (Abs b) where
  suggest b1 b2 = suggest (absName b1) (absName b2)

instance Suggest String (Abs b) where
  suggest x b = suggest x (absName b)

instance Suggest Name (Abs b) where
  suggest n b = suggest (nameToArgName n) (absName b)

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
  case ignoreSharing v of
    Var   i es -> Just (Var   i, es)
    Def   f es -> Just (Def   f, es)
    MetaV x es -> Just (MetaV x, es)
    Con{}      -> Nothing
    Lit{}      -> Nothing
    -- Andreas, 2016-04-13, Issue 1932: We convert λ x → x .f  into f
    Lam _ (Abs _ v)  -> case ignoreSharing v of
      Var 0 [Proj _o f] -> Just (Def f, [])
      _ -> Nothing
    Lam{}      -> Nothing
    Pi{}       -> Nothing
    Sort{}     -> Nothing
    Level{}    -> Nothing
    DontCare{} -> Nothing
    Shared{}   -> __IMPOSSIBLE__

{- PROBABLY USELESS
getElims :: Term -> (Elims -> Term, Elims)
getElims v = maybe default id $ hasElims v
  where
    default = (\ [] -> v, [])
-}

-- | Drop 'Apply' constructor. (Unsafe!)
argFromElim :: Elim' a -> Arg a
argFromElim (Apply u) = u
argFromElim Proj{}    = __IMPOSSIBLE__

-- | Drop 'Apply' constructor. (Safe)
isApplyElim :: Elim' a -> Maybe (Arg a)
isApplyElim (Apply u) = Just u
isApplyElim Proj{}    = Nothing

-- | Drop 'Apply' constructors. (Safe)
allApplyElims :: [Elim' a] -> Maybe [Arg a]
allApplyElims = mapM isApplyElim

-- | Split at first non-'Apply'
splitApplyElims :: [Elim' a] -> ([Arg a], [Elim' a])
splitApplyElims (Apply u : es) = mapFst (u :) $ splitApplyElims es
splitApplyElims es             = ([], es)

class IsProjElim e where
  isProjElim  :: e -> Maybe (ProjOrigin, QName)

instance IsProjElim Elim where
  isProjElim (Proj o d) = Just (o, d)
  isProjElim Apply{}    = Nothing

-- | Discard @Proj f@ entries.
dropProjElims :: IsProjElim e => [e] -> [e]
dropProjElims = filter (isNothing . isProjElim)

-- | Discards @Proj f@ entries.
argsFromElims :: Elims -> Args
argsFromElims = map argFromElim . dropProjElims

-- | Drop 'Proj' constructors. (Safe)
allProjElims :: Elims -> Maybe [(ProjOrigin, QName)]
allProjElims = mapM isProjElim

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
  empty = Clause empty empty empty empty empty empty False
  null (Clause _ _ tel pats body _ _)
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

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} (Foldable t, TermSize a) => TermSize (t a) where
#else
instance (Foldable t, TermSize a) => TermSize (t a) where
#endif
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
    Shared p    -> tsize (derefPtr p)

instance TermSize Sort where
  tsize s = case s of
    Type l    -> 1 + tsize l
    Prop      -> 1
    Inf       -> 1
    SizeUniv  -> 1
    DLub s s' -> 1 + tsize s + tsize s'

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
  tsize EmptyS             = 1
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
    Shared p    -> Shared $ updatePtr killRange p

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
    Prop       -> Prop
    Inf        -> Inf
    SizeUniv   -> SizeUniv
    Type a     -> killRange1 Type a
    DLub s1 s2 -> killRange2 DLub s1 s2

instance KillRange Substitution where
  killRange IdS                  = IdS
  killRange EmptyS               = EmptyS
  killRange (Wk n rho)           = killRange1 (Wk n) rho
  killRange (t :# rho)           = killRange2 (:#) t rho
  killRange (Strengthen err rho) = killRange1 (Strengthen err) rho
  killRange (Lift n rho)         = killRange1 (Lift n) rho

instance KillRange ConPatternInfo where
  killRange (ConPatternInfo mr mt) = killRange1 (ConPatternInfo mr) mt

instance KillRange DBPatVar where
  killRange (DBPatVar x i) = killRange2 DBPatVar x i

instance KillRange a => KillRange (Pattern' a) where
  killRange p =
    case p of
      VarP x           -> killRange1 VarP x
      DotP v           -> killRange1 DotP v
      ConP con info ps -> killRange3 ConP con info ps
      LitP l           -> killRange1 LitP l
      ProjP o q        -> killRange1 (ProjP o) q

instance KillRange Clause where
  killRange (Clause rl rf tel ps body t catchall) =
    killRange7 Clause rl rf tel ps body t catchall

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
  prettyPrec p rho = pr p rho
    where
    pr p rho = case rho of
      IdS              -> text "idS"
      EmptyS           -> text "emptyS"
      t :# rho         -> mparens (p > 2) $ sep [ pr 2 rho P.<> text ",", prettyPrec 3 t ]
      Strengthen _ rho -> mparens (p > 9) $ text "strS" <+> pr 10 rho
      Wk n rho         -> mparens (p > 9) $ text ("wkS " ++ show n) <+> pr 10 rho
      Lift n rho       -> mparens (p > 9) $ text ("liftS " ++ show n) <+> pr 10 rho

instance Pretty Term where
  prettyPrec p v =
    case ignoreSharing v of
      Var x els -> text ("@" ++ show x) `pApp` els
      Lam ai b   ->
        mparens (p > 0) $
        sep [ text "λ" <+> prettyHiding ai id (text . show . absName $ b) <+> text "->"
            , nest 2 $ pretty (unAbs b) ]
      Lit l                -> pretty l
      Def q els            -> text (show q) `pApp` els
      Con c ci vs          -> text (show $ conName c) `pApp` map Apply vs
      Pi a (NoAbs _ b)     -> mparens (p > 0) $
        sep [ prettyPrec 1 (unDom a) <+> text "->"
            , nest 2 $ pretty b ]
      Pi a b               -> mparens (p > 0) $
        sep [ pDom (domInfo a) (text (absName b) <+> text ":" <+> pretty (unDom a)) <+> text "->"
            , nest 2 $ pretty (unAbs b) ]
      Sort s      -> prettyPrec p s
      Level l     -> prettyPrec p l
      MetaV x els -> pretty x `pApp` els
      DontCare v  -> prettyPrec p v
      Shared{}    -> __IMPOSSIBLE__
    where
      pApp d els = mparens (not (null els) && p > 9) $
                   sep [d, nest 2 $ fsep (map (prettyPrec 10) els)]

pDom :: LensHiding a => a -> Doc -> Doc
pDom i =
  case getHiding i of
    NotHidden -> parens
    Hidden    -> braces
    Instance  -> braces . braces

instance Pretty Clause where
  pretty Clause{clauseTel = tel, namedClausePats = ps, clauseBody = b, clauseType = t} =
    sep [ pretty tel <+> text "|-"
        , nest 2 $ sep [ fsep (map (prettyPrec 10) ps) <+> text "="
                       , nest 2 $ pBody b t ] ]
    where
      pBody Nothing _ = text "(absurd)"
      pBody (Just b) Nothing  = pretty b
      pBody (Just b) (Just t) = sep [ pretty b <+> text ":", nest 2 $ pretty t ]

instance Pretty a => Pretty (Tele (Dom a)) where
  pretty tel = fsep [ pDom a (text x <+> text ":" <+> pretty (unDom a)) | (x, a) <- telToList tel ]
    where
      telToList EmptyTel = []
      telToList (ExtendTel a tel) = (absName tel, a) : telToList (unAbs tel)

instance Pretty Level where
  prettyPrec p (Max as) =
    case as of
      []  -> prettyPrec p (ClosedLevel 0)
      [a] -> prettyPrec p a
      _   -> mparens (p > 9) $ List.foldr1 (\a b -> text "lub" <+> a <+> b) $ map (prettyPrec 10) as

instance Pretty PlusLevel where
  prettyPrec p l =
    case l of
      ClosedLevel n -> sucs p n $ \_ -> text "lzero"
      Plus n a      -> sucs p n $ \p -> prettyPrec p a
    where
      sucs p 0 d = d p
      sucs p n d = mparens (p > 9) $ text "lsuc" <+> sucs 10 (n - 1) d

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
      Type (Max []) -> text "Set"
      Type (Max [ClosedLevel n]) -> text $ "Set" ++ show n
      Type l -> mparens (p > 9) $ text "Set" <+> prettyPrec 10 l
      Prop -> text "Prop"
      Inf -> text "Setω"
      SizeUniv -> text "SizeUniv"
      DLub s b -> mparens (p > 9) $
        text "dlub" <+> prettyPrec 10 s
                    <+> parens (sep [ text ("λ " ++ show (absName b) ++ " ->")
                                    , nest 2 $ pretty (unAbs b) ])

instance Pretty Type where
  prettyPrec p (El _ a) = prettyPrec p a

instance Pretty Elim where
  prettyPrec p (Apply v)    = prettyPrec p v
  prettyPrec _ (Proj _o x)  = text ("." ++ show x)

instance Pretty DBPatVar where
  prettyPrec _ x = text $ patVarNameToString (dbPatVarName x) ++ "@" ++ show (dbPatVarIndex x)

instance Pretty a => Pretty (Pattern' a) where
  prettyPrec n (VarP x)      = prettyPrec n x
  prettyPrec _ (DotP t)      = text "." P.<> prettyPrec 10 t
  prettyPrec n (ConP c i nps)= mparens (n > 0) $
    text (show $ conName c) <+> fsep (map pretty ps)
    where ps = map (fmap namedThing) nps
  -- -- Version with printing record type:
  -- prettyPrec _ (ConP c i ps) = (if b then braces else parens) $ prTy $
  --   text (show $ conName c) <+> fsep (map (pretty . namedArg) ps)
  --   where
  --     b = maybe False (== ConOSystem) $ conPRecord i
  --     prTy d = caseMaybe (conPType i) d $ \ t -> d  <+> text ":" <+> pretty t
  prettyPrec _ (LitP l)      = text (show l)
  prettyPrec _ (ProjP _o q)  = text ("." ++ show q)

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
    Shared{}   -> ()

instance NFData Type where
  rnf (El s v) = rnf (s, v)

instance NFData Sort where
  rnf s = case s of
    Type l   -> rnf l
    Prop     -> ()
    Inf      -> ()
    SizeUniv -> ()
    DLub a b -> rnf (a, unAbs b)

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
