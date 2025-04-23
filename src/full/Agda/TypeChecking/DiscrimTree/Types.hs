module Agda.TypeChecking.DiscrimTree.Types where

import Control.DeepSeq

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Data.Map.Strict (Map)
import Data.Set (Set)

import GHC.Generics (Generic)

import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Common

import Agda.Utils.Impossible
import Agda.Utils.Null

data Key
  = RigidK {-# UNPACK #-} !QName {-# UNPACK #-} !Int
    -- ^ Rigid symbols (constructors, data types, record types,
    -- postulates) identified by a QName.
  | LocalK {-# UNPACK #-} !Int {-# UNPACK #-} !Int
    -- ^ Local variables.

  | PiK Hiding
    -- ^ Dependent function types. The domain will be represented
    -- accurately, for the case of a genuine dependent function type,
    -- the codomain will be a dummy.

  | ConstK
    -- ^ Constant lambdas.

  | SortK
    -- ^ Universes.

  | FlexK
  -- ^ Anything else.
  deriving (Show, Eq, Ord, Generic)

instance NFData Key

-- | A 'Term'-indexed associative data structure supporting
-- /approximate/ (conservative) lookup. Rather than using a @Trie@ keyed
-- by 'Key' directly, a 'DiscrimTree' is instead represented more like a
-- /case/ tree.
--
-- This allows us to exploit the fact that instance selection often
-- focuses on a small part of the term: Only that critical chain is
-- represented in the tree. As an example, level parameters are unlikely
-- to contribute to narrowing a search problem, so it would be wasteful
-- to have an indirection in the tree for every 'FlexK' standing for a
-- level parameter.
data DiscrimTree a
  = EmptyDT
    -- ^ The empty discrimination tree.
  | DoneDT (Set a)
    -- ^ Succeed with a given set of values.
  | CaseDT
    -- ^ Do case analysis on a term. 'CaseDT' is scoped in the same way
    -- as fast case trees for the abstract machine: When matching
    -- actually succeeds, the variable that was matched gets replaced by
    -- its arguments directly in the context.
      {-# UNPACK #-} !Int       -- ^ The variable to case on.
      (Map Key (DiscrimTree a)) -- ^ The proper branches.
      (DiscrimTree a)           -- ^ A further tree, which should always be explored.
  deriving (Generic, Eq, Show)

{-
The extra continuation to CaseDT is used to represent instance tables
which have non-trivial overlap, e.g.

  instance
    a : Foo X ?
    b : Foo ? X

If we commited to the {a} branch of the discrimination tree, then we
would miss {b} entirely. Note that an "obvious" overlap like

  instance
    a : Bar X
    b : Bar X

would be represented as

  case 0 of
    Bar → case 0 of
      X → done {a, b}

and the extra continuation would be empty.
-}

instance NFData a => NFData (DiscrimTree a)

instance (KillRange a, Ord a) => KillRange (DiscrimTree a) where
  killRange = \case
    EmptyDT      -> EmptyDT
    DoneDT s     -> killRangeN DoneDT s
    CaseDT i k o -> killRangeN CaseDT i k o

instance Null (DiscrimTree a) where
  empty = EmptyDT
  null = \case
    EmptyDT -> True
    _       -> False

-- | Merge a pair of discrimination trees. This function tries to build
-- the minimal discrimination tree that yields the union of the inputs'
-- results, though it does so slightly naïvely, without considerable
-- optimisations (e.g. it does not turn single-alternative 'CaseDT's
-- into 'DoneDT's).
mergeDT :: Ord a => DiscrimTree a -> DiscrimTree a -> DiscrimTree a
mergeDT EmptyDT    x = x
mergeDT (DoneDT s) x = case x of
  EmptyDT       -> DoneDT s
  DoneDT s'     -> DoneDT (s <> s')
  CaseDT i bs x -> CaseDT i bs (mergeDT (DoneDT s) x)
mergeDT (CaseDT i bs els) x = case x of
  EmptyDT  -> CaseDT i bs els
  DoneDT s -> CaseDT i bs (mergeDT (DoneDT s) els)
  CaseDT j bs' els' -> case compare i j of
    EQ -> CaseDT j (Map.unionWith mergeDT bs bs') (mergeDT els els')
    LT -> CaseDT i bs (mergeDT els (CaseDT j bs' els'))
    GT -> CaseDT j bs' (mergeDT els' (CaseDT i bs els))

instance Ord a => Semigroup (DiscrimTree a) where
  (<>) = mergeDT

instance Ord a => Monoid (DiscrimTree a) where
  mempty = EmptyDT

-- | Construct the case tree corresponding to only performing proper
-- matches on the given key. In this context, a "proper match" is any
-- 'Key' that is not 'FlexK'.
singletonDT :: [Key] -> a -> DiscrimTree a
singletonDT key val = go 0 key where
  go focus []         = DoneDT $ Set.singleton val
  go focus (FlexK:ts) = go (focus + 1) ts
  go focus (t:ts)     = CaseDT focus (Map.singleton t (go focus ts)) EmptyDT
