{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Agda.Utils.PartialOrd where

import Data.Functor
import Data.Monoid
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Test.QuickCheck.All

-- import Agda.Utils.List
import Agda.Utils.SemiRing
import Agda.Utils.TestHelpers
import Agda.Utils.QuickCheck

-- | The result of comparing two things (of the same type).
data PartialOrdering
  = POLT  -- ^ Less than.
  | POLE  -- ^ Less or equal than.
  | POEQ  -- ^ Equal
  | POGE  -- ^ Greater or equal.
  | POGT  -- ^ Greater than.
  | POAny -- ^ No information (incomparable).
  deriving (Eq, Show, Enum, Bounded)

-- | Opposites.
--
--   @related a po b@ iff @related b (oppPO po) a@.

oppPO :: PartialOrdering -> PartialOrdering
oppPO POLT  = POGT
oppPO POLE  = POGE
oppPO POEQ  = POEQ
oppPO POGE  = POLE
oppPO POGT  = POLT
oppPO POAny = POAny

-- | What if either of two facts hold?
--   @x R y || x S y@
orPO :: PartialOrdering -> PartialOrdering -> PartialOrdering

orPO POAny _   = POAny   -- Shortcut if no information on first.

orPO POLT POLT = POLT
orPO POLT POLE = POLE
orPO POLT POEQ = POLE

orPO POLE POLT = POLE
orPO POLE POLE = POLE
orPO POLE POEQ = POLE

orPO POEQ POLT = POLE
orPO POEQ POLE = POLE
orPO POEQ POEQ = POEQ
orPO POEQ POGE = POGE
orPO POEQ POGT = POGE

orPO POGE POEQ = POGE
orPO POGE POGE = POGE
orPO POGE POGT = POGE

orPO POGT POEQ = POGE
orPO POGT POGE = POGE
orPO POGT POGT = POGT

orPO _    _    = POAny

-- | Chains (transitivity) @x R y S z@.
--   Also: conjunction (trying to get the best information out).

seqPO POAny _   = POAny  -- Shortcut if no information on first.
seqPO POEQ p    = p      -- No need to look at second if first is neutral.

seqPO POLT POLT = POLT
seqPO POLT POLE = POLT
seqPO POLT POEQ = POLT

seqPO POLE POLT = POLT
seqPO POLE POLE = POLE
seqPO POLE POEQ = POLE

seqPO POGE POEQ = POGE
seqPO POGE POGE = POGE
seqPO POGE POGT = POGT

seqPO POGT POEQ = POGT
seqPO POGT POGE = POGT
seqPO POGT POGT = POGT

seqPO _    _    = POAny

-- | Partial ordering forms a monoid under sequencing.
instance Monoid PartialOrdering where
  mempty  = POEQ
  mappend = seqPO

-- | Partial ordering forms a semiring under supremum (disjunction)
--   and composition (transitivity, sequencing)
instance SemiRing PartialOrdering where
  oplus  = orPO
  otimes = seqPO

-- | Embed 'Ordering'.
fromOrdering :: Ordering -> PartialOrdering
fromOrdering LT = POLT
fromOrdering EQ = POEQ
fromOrdering GT = POGT

-- | Represent a non-empty disjunction of 'Ordering's as 'PartialOrdering'.
fromOrderings :: [Ordering] -> PartialOrdering
fromOrderings = foldr1 orPO . map fromOrdering

-- | A 'PartialOrdering' information is a disjunction of 'Ordering' informations.
toOrderings :: PartialOrdering -> [Ordering]
toOrderings POLT  = [LT]
toOrderings POLE  = [LT, EQ]
toOrderings POEQ  = [EQ]
toOrderings POGE  = [EQ, GT]
toOrderings POGT  = [GT]
toOrderings POAny = [LT, EQ, GT]

-- * Comparison with partial result

type Comparable a = a -> a -> PartialOrdering

-- | Decidable partial orderings.
class PartialOrd a where
  comparable :: Comparable a

-- | Any 'Ord' is a 'PartialOrd'.
comparableOrd :: Ord a => Comparable a
comparableOrd x y = fromOrdering $ compare x y

-- | Are two elements related in a specific way?
--
--   @related a o b@ holds iff @comparable a b@ is contained in @o@.

related :: PartialOrd a => a -> PartialOrdering -> a -> Bool
related a o b = null $ toOrderings (comparable a b) \\ toOrderings o

-- * Generic partially ordered types.

instance PartialOrd () where
  comparable _ _ = POEQ

-- | 'Nothing' and @'Just' _@ are unrelated.
--
--   Partial ordering for @Maybe a@ is the same as for @Either () a@.

instance PartialOrd a => PartialOrd (Maybe a) where
  comparable mx my = case (mx, my) of
    (Nothing, Nothing) -> POEQ
    (Nothing, Just{} ) -> POAny
    (Just{} , Nothing) -> POAny
    (Just x , Just y ) -> comparable x y

-- | Partial ordering for disjoint sums: @Left _@ and @Right _@ are unrelated.

instance (PartialOrd a, PartialOrd b) => PartialOrd (Either a b) where
  comparable mx my = case (mx, my) of
    (Left  x, Left  y) -> comparable x y
    (Left  x, Right y) -> POAny
    (Right x, Left  y) -> POAny
    (Right x, Right y) -> comparable x y

-- | Pointwise partial ordering for tuples.
--
--   @related (x1,x2) o (y1,y2)@ iff @related x1 o x2@ and @related y1 o y2@.

instance (PartialOrd a, PartialOrd b) => PartialOrd (a, b) where
  comparable (x1, x2) (y1, y2) =
    comparable x1 y1 `mappend`
    comparable x2 y2

-- | Pointwise comparison wrapper.

newtype Pointwise a = Pointwise { pointwise :: a }
  deriving (Eq, Show, Functor)

-- | Lifting the pointwise ordering for tuples to lists.
--
--   There are other partial orderings for lists, e.g., prefix, sublist, subset.

instance PartialOrd a => PartialOrd (Pointwise [a]) where
  comparable xs ys = comparable (unconsPointwise $ pointwise xs)
                                (unconsPointwise $ pointwise ys)
    where unconsPointwise []       = Nothing
          unconsPointwise (x : xs) = Just (x, Pointwise xs)

-- | Inclusion comparison wrapper.

newtype Inclusion a = Inclusion { inclusion :: a }
  deriving (Eq, Ord, Show, Functor)

-- | Sublist for ordered lists.

instance (Ord a) => PartialOrd (Inclusion [a]) where
  comparable (Inclusion xs) (Inclusion ys) = merge POEQ xs ys
    where
      -- We use an accumulator in order to short-cut computation
      -- once we know the lists are incomparable.
      merge' POAny xs ys = POAny
      merge' o     xs ys = merge o xs ys
      merge o [] [] = o
      merge o [] ys = mappend o POLT
      merge o xs [] = mappend o POGT
      merge o xs@(x:xs') ys@(y:ys') =
        case compare x y of
          -- xs has an element that ys does not have => POGT
          LT -> merge' (mappend o POGT) xs' ys
          -- equal elements can be cancelled
          EQ -> merge o xs' ys'
          -- ys has an element that xs does not have => POLT
          GT -> merge' (mappend o POLT) xs ys'

-- | Sets are partially ordered by inclusion.

instance Ord a => PartialOrd (Inclusion (Set a)) where
  comparable s t = comparable (Set.toAscList <$> s) (Set.toAscList <$> t)

-- * PartialOrdering is itself partially ordered!

-- | Less is ``less general'' (i.e., more precise).
instance PartialOrd PartialOrdering where
  -- working our way down: POAny is top
  comparable POAny POAny = POEQ
  comparable POAny _     = POGT
  comparable _     POAny = POLT
  -- next are the fuzzy notions POLE and POGE
  comparable POLE  POLE  = POEQ
  comparable POLE  POLT  = POGT
  comparable POLE  POEQ  = POGT
  comparable POGE  POGE  = POEQ
  comparable POGE  POGT  = POGT
  comparable POGE  POEQ  = POGT
  -- lowest are the precise notions POLT POEQ POGT
  comparable POLT  POLT  = POEQ
  comparable POLT  POLE  = POLT
  comparable POEQ  POEQ  = POEQ
  comparable POEQ  POLE  = POLT
  comparable POEQ  POGE  = POLT
  comparable POGT  POGT  = POEQ
  comparable POGT  POGE  = POLT
  -- anything horizontal is not comparable
  comparable _     _     = POAny

-- * Properties

instance Arbitrary PartialOrdering where
  arbitrary = arbitraryBoundedEnum

-- | We test our properties on integer sets ordered by inclusion.

newtype ISet = ISet { iset :: Inclusion (Set Int) }
  deriving (Eq, Ord, PartialOrd, Show)

instance Arbitrary ISet where
  arbitrary = ISet . Inclusion . Set.fromList <$> arbitrary

-- | Any two elements are 'related' in the way 'comparable' computes.
prop_comparable_related (ISet a) (ISet b) =
  related a o b where o = comparable a b

-- | @flip comparable a b == oppPO (comparable a b)@
prop_oppPO (ISet a) (ISet b) =
  comparable a b == oppPO (comparable b a)

-- | Auxiliary function: lists to sets = sorted duplicate-free lists.
sortUniq = Set.toAscList . Set.fromList

-- | 'orPO' amounts to the union of the associated 'Ordering' sets.
--   Except that 'orPO POLT POGT == POAny' which should also include 'POEQ'.
prop_orPO_sound p q =
  (p `orPO` q) == fromOrderings (toOrderings p ++ toOrderings q)

-- | 'orPO' is associative.
prop_associative_orPO = associative orPO

-- | 'orPO' is communtative.
prop_commutative_orPO = commutative orPO

-- | The dominant element wrt. 'orPO' is 'POAny'.
prop_zero_orPO = isZero POAny orPO

-- | Soundness of 'seqPO'.
--
--   As QuickCheck test, this property is inefficient, see 'prop_seqPO'.
property_seqPO (ISet a) o (ISet b) p (ISet c) =
  related a o b && related b p c ==> related a (seqPO o p) c

-- | A more efficient way of stating soundness of 'seqPO'.
prop_seqPO (ISet a) (ISet b) (ISet c) = related a o c
  where o = comparable a b `seqPO` comparable b c

-- | The unit of 'seqPO' is 'POEQ'.
prop_identity_seqPO = identity POEQ seqPO

-- | The zero of 'seqPO' is 'POAny'.
prop_zero_seqPO = isZero POAny seqPO

-- | 'seqPO' is associative.
prop_associative_seqPO = associative seqPO

-- | 'seqPO' is also commutative.
prop_commutative_seqPO = commutative seqPO

-- | 'seqPO' distributes over 'orPO'.
prop_distributive_seqPO_orPO = distributive seqPO orPO

-- | The result of 'toOrderings' is a sorted list without duplicates.
prop_sorted_toOrderings p =
  sortUniq os == os where os = toOrderings p

-- | From 'Ordering' to 'PartialOrdering' and back is the identity.
prop_toOrderings_after_fromOrdering o =
  toOrderings (fromOrdering o) == [o]

-- | From 'PartialOrdering' to 'Orderings' and back is the identity.
prop_fromOrderings_after_toOrderings p =
  fromOrderings (toOrderings p) == p

-- | From 'Orderings' to 'PartialOrdering' and back is the identity.
--   Except for @[LT,GT]@ which is a non-canonical representative of 'POAny'.
prop_toOrderings_after_fromOrderings (NonEmpty os) =
  Set.fromList os  `Set.isSubsetOf`
  Set.fromList (toOrderings (fromOrderings os))

-- | Pairs are related iff both components are related.

prop_related_pair (ISet x1) (ISet x2) (ISet y1) (ISet y2) o =
  related (x1,x2) o (y1,y2) == (related x1 o y1 && related x2 o y2)

-- | Comparing 'PartialOrdering's amounts to compare their representation as
--   'Ordering' sets.

prop_comparable_PartialOrdering p q =
  comparable p q == comparable (to p) (to q)
    where to = Inclusion . toOrderings

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'quickCheckAll'.
--
--   Using 'quickCheckAll' is convenient and superior to the manual
--   enumeration of tests, since the name of the property is
--   added automatically.

tests :: IO Bool
tests = do
  putStrLn "Agda.Utils.PartialOrd"
  $quickCheckAll

-- tests' :: IO Bool
-- tests' = runTests "Agda.Utils.PartialOrd"
--   [ quickCheck' prop_comparable_related
--   , quickCheck' prop_oppPO
--   , quickCheck' prop_seqPO
--   , quickCheck' prop_assoc_seqPO
--   , quickCheck' prop_related_pair
--   ]
