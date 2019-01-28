{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | Computing the free variables of a term.
--
-- The distinction between rigid and strongly rigid occurrences comes from:
--   Jason C. Reed, PhD thesis, 2009, page 96 (see also his LFMTP 2009 paper)
--
-- The main idea is that x = t(x) is unsolvable if x occurs strongly rigidly
-- in t.  It might have a solution if the occurrence is not strongly rigid, e.g.
--
--   x = \f -> suc (f (x (\ y -> k)))  has  x = \f -> suc (f (suc k))
--
-- [Jason C. Reed, PhD thesis, page 106]
--
-- Under coinductive constructors, occurrences are never strongly rigid.
-- Also, function types and lambdas do not establish strong rigidity.
-- Only inductive constructors do so.
-- (See issue 1271).

module Agda.TypeChecking.Free
    ( FreeVars(..)
    , VarCounts(..)
    , Free
    , IsVarSet(..)
    , IgnoreSorts(..)
    , runFree , rigidVars, relevantVars, allVars
    , allFreeVars, allFreeVarsWithOcc
    , allRelevantVars, allRelevantVarsIgnoring
    , freeIn, freeInIgnoringSorts, isBinderUsed
    , relevantIn, relevantInIgnoringSortAnn
    , Occurrence(..)
    , VarOcc(..)
    , occurrence
    , closed
    , freeVars -- only for testing
    , freeVars'
    , MetaSet
    ) where

import Prelude hiding (null)

import Control.Monad.Reader ()

import Data.Maybe ()
import Data.Monoid ( Monoid, mempty, mappend, mconcat )
import Data.Semigroup ( Semigroup, (<>), Any(..), All(..) )
import Data.IntSet (IntSet)
import qualified Data.IntSet as Set
import Data.IntMap (IntMap)
import qualified Data.IntMap as Map
import Data.Set ()
import Data.Proxy ()

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Internal

import Agda.TypeChecking.Free.Lazy
  ( Free(..)
  , VarOcc(..), topVarOcc, TheVarMap, theVarMap, IgnoreSorts(..), Variable, SingleVar
  , MetaSet, IsVarSet(..), runFreeM
  )
import qualified Agda.TypeChecking.Free.Lazy as Free

import Agda.Utils.Null
import Agda.Utils.Singleton

type VarSet = IntSet

-- | Free variables of a term, (disjointly) partitioned into strongly and
--   and weakly rigid variables, flexible variables and irrelevant variables.
data FreeVars = FV
  { stronglyRigidVars :: VarSet
    -- ^ Variables under only and at least one inductive constructor(s).
  , unguardedVars     :: VarSet
    -- ^ Variables at top or only under inductive record constructors
    --   λs and Πs.
    --   The purpose of recording these separately is that they
    --   can still become strongly rigid if put under a constructor
    --   whereas weakly rigid ones stay weakly rigid.
  , weaklyRigidVars   :: VarSet
    -- ^ Ordinary rigid variables, e.g., in arguments of variables or functions.
  , flexibleVars      :: IntMap MetaSet
    -- ^ Variables occuring in arguments of metas.
    --   These are only potentially free, depending how the meta variable is instantiated.
    --   The set contains the id's of the meta variables that this variable is an argument to.
  , irrelevantVars    :: VarSet
    -- ^ Variables in irrelevant arguments and under a @DontCare@, i.e.,
    --   in irrelevant positions.
  } deriving (Eq, Show)

mapUGV :: (VarSet -> VarSet) -> FreeVars -> FreeVars
mapUGV f fv = fv { unguardedVars = f $ unguardedVars fv }

-- | Rigid variables: either strongly rigid, unguarded, or weakly rigid.
rigidVars :: FreeVars -> VarSet
rigidVars fv = Set.unions
  [ stronglyRigidVars fv
  ,     unguardedVars fv
  ,   weaklyRigidVars fv
  ]

-- | All but the irrelevant variables.
relevantVars :: FreeVars -> VarSet
relevantVars fv = Set.unions [rigidVars fv, Map.keysSet (flexibleVars fv)]

-- | @allVars fv@ includes irrelevant variables.
allVars :: FreeVars -> VarSet
allVars fv = Set.unions [relevantVars fv, irrelevantVars fv]

data Occurrence
  = NoOccurrence
  | Irrelevantly
  | StronglyRigid     -- ^ Under at least one and only inductive constructors.
  | Unguarded         -- ^ In top position, or only under inductive record constructors.
  | WeaklyRigid       -- ^ In arguments to variables and definitions.
  | Flexible MetaSet  -- ^ In arguments of metas.
  deriving (Eq,Show)

-- | Compute an occurrence of a single variable in a piece of internal syntax.
occurrence :: Free a => Nat -> a -> Occurrence
occurrence x v = occurrenceFV x $ freeVars v

-- | Extract occurrence of a single variable from computed free variables.
occurrenceFV :: Nat -> FreeVars -> Occurrence
occurrenceFV x fv
  | x `Set.member` stronglyRigidVars fv = StronglyRigid
  | x `Set.member` unguardedVars     fv = Unguarded
  | x `Set.member` weaklyRigidVars   fv = WeaklyRigid
  | Just ms <- Map.lookup x (flexibleVars fv) = Flexible ms
  | x `Set.member` irrelevantVars    fv = Irrelevantly
  | otherwise                           = NoOccurrence

-- | Mark variables as flexible.  Useful when traversing arguments of metas.
flexible :: MetaSet -> FreeVars -> FreeVars
flexible ms fv =
    fv { stronglyRigidVars = Set.empty
       , unguardedVars     = Set.empty
       , weaklyRigidVars   = Set.empty
       , flexibleVars      = Map.unionsWith mappend
                               [ Map.fromSet (const ms) (rigidVars fv)
                               , fmap (mappend ms) (flexibleVars fv) ]
       }

-- | Mark rigid variables as non-strongly.  Useful when traversing arguments of variables.
weakly :: FreeVars -> FreeVars
weakly fv = fv
  { stronglyRigidVars = Set.empty
  , unguardedVars     = Set.empty
  , weaklyRigidVars   = rigidVars fv
  }

-- | Mark unguarded variables as strongly rigid.  Useful when traversing arguments of inductive constructors.
strongly :: FreeVars -> FreeVars
strongly fv = fv
  { stronglyRigidVars = stronglyRigidVars fv `Set.union` unguardedVars fv
  , unguardedVars     = Set.empty
  }

-- | Mark all free variables as irrelevant.
irrelevantly :: FreeVars -> FreeVars
irrelevantly fv = empty { irrelevantVars = allVars fv }

-- | Pointwise union.
union :: FreeVars -> FreeVars -> FreeVars
union (FV sv1 gv1 rv1 fv1 iv1) (FV sv2 gv2 rv2 fv2 iv2) =
  FV (Set.union sv1 sv2) (Set.union gv1 gv2) (Set.union rv1 rv2) (Map.unionWith mappend fv1 fv2) (Set.union iv1 iv2)

unions :: [FreeVars] -> FreeVars
unions = foldr union empty

instance Null FreeVars where
  empty = FV Set.empty Set.empty Set.empty Map.empty Set.empty
  null (FV a b c d e) = null a && null b && null c && null d && null e

-- | Free variable sets form a monoid under 'union'.
instance Semigroup FreeVars where
  (<>) = union

instance Monoid FreeVars where
  mempty  = empty
  mappend = (<>)
  mconcat = unions

instance Singleton Variable FreeVars where
  singleton i = mapUGV (Set.insert i) mempty

instance IsVarSet FreeVars where
  withVarOcc (VarOcc o r) = goOcc o . goRel r
    where
      goOcc o = case o of
        Free.Flexible ms   -> flexible ms
        Free.WeaklyRigid   -> weakly
        Free.Unguarded     -> id
        Free.StronglyRigid -> strongly
      goRel r = case r of
        Relevant   -> id
        NonStrict  -> id    -- we don't track non-strict in FreeVars
        Irrelevant -> irrelevantly

-- In most cases we don't care about the VarOcc.

instance IsVarSet VarSet where withVarOcc _ = id
instance IsVarSet [Int]  where withVarOcc _ = id
instance IsVarSet Any    where withVarOcc _ = id
instance IsVarSet All    where withVarOcc _ = id

newtype VarCounts = VarCounts { varCounts :: IntMap Int }

instance Semigroup VarCounts where
  VarCounts fv1 <> VarCounts fv2 = VarCounts (Map.unionWith (+) fv1 fv2)

instance Monoid VarCounts where
  mempty = VarCounts Map.empty
  mappend = (<>)

instance IsVarSet VarCounts where withVarOcc _ = id

instance Singleton Variable VarCounts where
  singleton i = VarCounts $ Map.singleton i 1

-- * Collecting free variables.

-- | Doesn't go inside solved metas, but collects the variables from a
-- metavariable application @X ts@ as @flexibleVars@.
{-# SPECIALIZE freeVars :: Free a => a -> FreeVars #-}
freeVars :: (IsVarSet c, Singleton Variable c, Free a) => a -> c
freeVars = freeVarsIgnore IgnoreNot

{-# SPECIALIZE freeVarsIgnore :: Free a => IgnoreSorts -> a -> FreeVars #-}
freeVarsIgnore :: (IsVarSet c, Singleton Variable c, Free a) =>
                  IgnoreSorts -> a -> c
freeVarsIgnore = runFree singleton

-- Specialization to typical monoids
{-# SPECIALIZE runFree :: Free a => SingleVar Any      -> IgnoreSorts -> a -> Any #-}
{-# SPECIALIZE runFree :: Free a => SingleVar FreeVars -> IgnoreSorts -> a -> FreeVars #-}
-- Specialization to Term
{-# SPECIALIZE runFree :: SingleVar Any      -> IgnoreSorts -> Term -> Any #-}
{-# SPECIALIZE runFree :: SingleVar FreeVars -> IgnoreSorts -> Term -> FreeVars #-}

-- | Compute free variables.
runFree :: (IsVarSet c, Free a) => SingleVar c -> IgnoreSorts -> a -> c
runFree single i t = -- bench $  -- Benchmarking is expensive (4% on std-lib)
  runFreeM single i (freeVars' t)

-- | Check if a variable is free, possibly ignoring sorts.
freeIn' :: Free a => IgnoreSorts -> Nat -> a -> Bool
freeIn' ig x t = getAny $ runFree (Any . (x ==)) ig t

{-# SPECIALIZE freeIn :: Nat -> Term -> Bool #-}
freeIn :: Free a => Nat -> a -> Bool
freeIn = freeIn' IgnoreNot

freeInIgnoringSorts :: Free a => Nat -> a -> Bool
freeInIgnoringSorts = freeIn' IgnoreAll

newtype RelevantIn a = RelevantIn {getRelevantIn :: a}
  deriving (Semigroup, Monoid)

instance IsVarSet a => IsVarSet (RelevantIn a) where
  withVarOcc o x
    | isIrrelevant (varRelevance o) = mempty
    | otherwise = RelevantIn $ withVarOcc o $ getRelevantIn x

relevantIn' :: Free a => IgnoreSorts -> Nat -> a -> Bool
relevantIn' ig x t = getAny . getRelevantIn $ runFree (RelevantIn . Any . (x ==)) ig t

relevantInIgnoringSortAnn :: Free a => Nat -> a -> Bool
relevantInIgnoringSortAnn = relevantIn' IgnoreInAnnotations

relevantIn :: Free a => Nat -> a -> Bool
relevantIn = relevantIn' IgnoreAll

-- | Is the variable bound by the abstraction actually used?
isBinderUsed :: Free a => Abs a -> Bool
isBinderUsed NoAbs{}   = False
isBinderUsed (Abs _ x) = 0 `freeIn` x

-- | Is the term entirely closed (no free variables)?
closed :: Free a => a -> Bool
closed t = getAll $ runFree (const $ All False) IgnoreNot t

-- | Collect all free variables.
allFreeVars :: Free a => a -> VarSet
allFreeVars = runFree Set.singleton IgnoreNot

-- | Collect all free variables together with information about their occurrence.
allFreeVarsWithOcc :: Free a => a -> TheVarMap
allFreeVarsWithOcc = theVarMap . runFree (singleton . (,topVarOcc)) IgnoreNot

-- | Collect all relevant free variables, possibly ignoring sorts.
allRelevantVarsIgnoring :: Free a => IgnoreSorts -> a -> VarSet
allRelevantVarsIgnoring ig = getRelevantIn . runFree (RelevantIn . Set.singleton) ig

-- | Collect all relevant free variables, excluding the "unused" ones.
allRelevantVars :: Free a => a -> VarSet
allRelevantVars = allRelevantVarsIgnoring IgnoreNot
