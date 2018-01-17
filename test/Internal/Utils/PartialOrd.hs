{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}

module Internal.Utils.PartialOrd
  ( ISet(ISet)
  , tests
  ) where

import Agda.Utils.PartialOrd

import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Internal.Helpers

------------------------------------------------------------------------------
-- * Properties

instance Arbitrary PartialOrdering where
  arbitrary = arbitraryBoundedEnum

-- | We test our properties on integer sets ordered by inclusion.

newtype ISet = ISet { iset :: Inclusion (Set Int) }
  deriving (Eq, Ord, PartialOrd, Show)

instance Arbitrary ISet where
  arbitrary = ISet . Inclusion . Set.fromList <$> listOf (choose (0, 8))

-- | Any two elements are 'related' in the way 'comparable' computes.
prop_comparable_related :: ISet -> ISet -> Bool
prop_comparable_related (ISet a) (ISet b) =
  related a o b where o = comparable a b

-- | @flip comparable a b == oppPO (comparable a b)@
prop_oppPO :: ISet -> ISet -> Bool
prop_oppPO (ISet a) (ISet b) =
  comparable a b == oppPO (comparable b a)

-- | Auxiliary function: lists to sets = sorted duplicate-free lists.
sortUniq :: [Ordering] -> [Ordering]
sortUniq = Set.toAscList . Set.fromList

-- | 'leqPO' is inclusion of the associated 'Ordering' sets.
prop_leqPO_sound :: PartialOrdering -> PartialOrdering -> Bool
prop_leqPO_sound p q =
  (p `leqPO` q) == null (toOrderings p \\ toOrderings q)

-- | 'orPO' amounts to the union of the associated 'Ordering' sets.
--   Except that 'orPO POLT POGT == POAny' which should also include 'POEQ'.
prop_orPO_sound :: PartialOrdering -> PartialOrdering -> Bool
prop_orPO_sound p q =
  (p `orPO` q) == fromOrderings (toOrderings p ++ toOrderings q)

-- | 'orPO' is associative.
prop_associative_orPO :: PartialOrdering -> PartialOrdering ->
                         PartialOrdering -> Bool
prop_associative_orPO = isAssociative orPO

-- | 'orPO' is commutative.
prop_commutative_orPO :: PartialOrdering -> PartialOrdering -> Bool
prop_commutative_orPO = isCommutative orPO

-- | 'orPO' is idempotent.
prop_idempotent_orPO :: PartialOrdering -> Bool
prop_idempotent_orPO = isIdempotent orPO

-- | The dominant element wrt. 'orPO' is 'POAny'.
prop_zero_orPO :: PartialOrdering -> Bool
prop_zero_orPO = isZero POAny orPO

-- | Soundness of 'seqPO'.
--
--   As QuickCheck test, this property is inefficient, see 'prop_seqPO'.
property_seqPO :: ISet -> PartialOrdering -> ISet -> PartialOrdering ->
                  ISet -> Property
property_seqPO (ISet a) o (ISet b) p (ISet c) =
  related a o b && related b p c ==> related a (seqPO o p) c

-- | A more efficient way of stating soundness of 'seqPO'.
prop_seqPO :: ISet -> ISet -> ISet -> Bool
prop_seqPO (ISet a) (ISet b) (ISet c) = related a o c
  where o = comparable a b `seqPO` comparable b c

-- | 'PartialOrdering' is a monoid, i.e. 'seqPO' is associative and
-- the unit of 'seqPO' is 'POEQ'.
prop_monoid_seqPO :: Property3 PartialOrdering
prop_monoid_seqPO = isMonoid

-- | The zero of 'seqPO' is 'POAny'.
prop_zero_seqPO :: PartialOrdering -> Bool
prop_zero_seqPO = isZero POAny seqPO

-- | 'seqPO' is also commutative.
prop_commutative_seqPO :: PartialOrdering -> PartialOrdering -> Bool
prop_commutative_seqPO = isCommutative seqPO

-- | 'seqPO' is idempotent.
prop_idempotent_seqPO :: PartialOrdering -> Bool
prop_idempotent_seqPO = isIdempotent seqPO

-- | 'seqPO' distributes over 'orPO'.
prop_distributive_seqPO_orPO :: PartialOrdering -> PartialOrdering ->
                                PartialOrdering -> Bool
prop_distributive_seqPO_orPO = isDistributive seqPO orPO

-- | The result of 'toOrderings' is a sorted list without duplicates.
prop_sorted_toOrderings :: PartialOrdering -> Bool
prop_sorted_toOrderings p =
  sortUniq os == os where os = toOrderings p

-- | From 'Ordering' to 'PartialOrdering' and back is the identity.
prop_toOrderings_after_fromOrdering :: Ordering -> Bool
prop_toOrderings_after_fromOrdering o =
  toOrderings (fromOrdering o) == [o]

-- | From 'PartialOrdering' to 'Orderings' and back is the identity.
prop_fromOrderings_after_toOrderings :: PartialOrdering -> Bool
prop_fromOrderings_after_toOrderings p =
  fromOrderings (toOrderings p) == p

-- | From 'Orderings' to 'PartialOrdering' and back is the identity.
--   Except for @[LT,GT]@ which is a non-canonical representative of 'POAny'.
prop_toOrderings_after_fromOrderings :: NonEmptyList Ordering -> Bool
prop_toOrderings_after_fromOrderings (NonEmpty os) =
  Set.fromList os  `Set.isSubsetOf`
  Set.fromList (toOrderings (fromOrderings os))

-- | Pairs are related iff both components are related.
prop_related_pair :: ISet -> ISet -> ISet -> ISet -> PartialOrdering -> Bool
prop_related_pair (ISet x1) (ISet x2) (ISet y1) (ISet y2) o =
  related (x1,x2) o (y1,y2) == (related x1 o y1 && related x2 o y2)

-- | Comparing 'PartialOrdering's amounts to compare their representation as
--   'Ordering' sets.

prop_comparable_PartialOrdering :: PartialOrdering -> PartialOrdering -> Bool

prop_comparable_PartialOrdering p q =
  comparable p q == comparable (to p) (to q)
    where to = Inclusion . toOrderings

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
--
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.Utils.PartialOrd" $allProperties
