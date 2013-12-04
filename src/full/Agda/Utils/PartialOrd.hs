{-# LANGUAGE FlexibleInstances #-}

module Agda.Utils.PartialOrd where

import Data.Foldable
import Data.Monoid

-- import Agda.Utils.List
import Agda.Utils.SemiRing

-- | The result of comparing two things (of the same type).
data PartialOrdering
  = POLT  -- ^ Less than.
  | POLE  -- ^ Less or equal than.
  | POEQ  -- ^ Equal
  | POGE  -- ^ Greater or equal.
  | POGT  -- ^ Greater than.
  | POAny -- ^ No information (incomparable).
  deriving (Eq, Show)

-- | What if either of two facts hold?
--   @x R y || x S y@
orPO :: PartialOrdering -> PartialOrdering -> PartialOrdering
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
seqPO POLT POLT = POLT
seqPO POLT POLE = POLT
seqPO POLT POEQ = POLT

seqPO POLE POLT = POLT
seqPO POLE POLE = POLE
seqPO POLE POEQ = POLE

seqPO POEQ p    = p

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
fromOrderings = foldMap fromOrdering

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

-- * Generic partially ordered types.

instance PartialOrd () where
  comparable _ _ = POEQ

instance PartialOrd a => PartialOrd (Maybe a) where
  comparable mx my = case (mx, my) of
    (Nothing, Nothing) -> POEQ
    (Nothing, Just{} ) -> POAny
    (Just{} , Nothing) -> POAny
    (Just x , Just y ) -> comparable x y

instance (PartialOrd a, PartialOrd b) => PartialOrd (Either a b) where
  comparable mx my = case (mx, my) of
    (Left  x, Left  y) -> comparable x y
    (Left  x, Right y) -> POAny
    (Right x, Left  y) -> POAny
    (Right x, Right y) -> comparable x y

instance (PartialOrd a, PartialOrd b) => PartialOrd (a, b) where
  comparable (x1, x2) (y1, y2) =
    comparable x1 y1 `mappend`
    comparable x2 y2

newtype Pointwise a = Pointwise { pointwise :: a }

instance PartialOrd a => PartialOrd (Pointwise [a]) where
  comparable xs ys = comparable (unconsPointwise $ pointwise xs)
                                (unconsPointwise $ pointwise ys)
    where unconsPointwise []       = Nothing
          unconsPointwise (x : xs) = Just (x, Pointwise xs)

-- * Properties

-- TODO!
