{-# LANGUAGE CPP #-}
module Agda.Utils.PartialOrd where


import Data.Maybe
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif
import Data.Set (Set)
import qualified Data.Set as Set

-- import Agda.Utils.List

-- | The result of comparing two things (of the same type).
data PartialOrdering
  = POLT  -- ^ Less than.
  | POLE  -- ^ Less or equal than.
  | POEQ  -- ^ Equal
  | POGE  -- ^ Greater or equal.
  | POGT  -- ^ Greater than.
  | POAny -- ^ No information (incomparable).
  deriving (Eq, Show, Enum, Bounded)

-- | Comparing the information content of two elements of
--   'PartialOrdering'.  More precise information is smaller.
--
--   Includes equality: @x `leqPO` x == True@.

leqPO :: PartialOrdering -> PartialOrdering -> Bool

leqPO _   POAny = True

leqPO POLT POLT = True
leqPO POLT POLE = True

leqPO POLE POLE = True

leqPO POEQ POLE = True
leqPO POEQ POEQ = True
leqPO POEQ POGE = True

leqPO POGE POGE = True

leqPO POGT POGT = True
leqPO POGT POGE = True

leqPO _ _ = False

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

-- | Combining two pieces of information (picking the least information).
--   Used for the dominance ordering on tuples.
--
--   @orPO@ is associative, commutative, and idempotent.
--   @orPO@ has dominant element @POAny@, but no neutral element.

orPO :: PartialOrdering -> PartialOrdering -> PartialOrdering

orPO POAny _   = POAny   -- Shortcut if no information on first.

orPO POLT POLT = POLT   -- idempotent
orPO POLT POLE = POLE
orPO POLT POEQ = POLE

orPO POLE POLT = POLE
orPO POLE POLE = POLE   -- idempotent
orPO POLE POEQ = POLE

orPO POEQ POLT = POLE
orPO POEQ POLE = POLE
orPO POEQ POEQ = POEQ   -- idempotent
orPO POEQ POGE = POGE
orPO POEQ POGT = POGE

orPO POGE POEQ = POGE
orPO POGE POGE = POGE   -- idempotent
orPO POGE POGT = POGE

orPO POGT POEQ = POGE
orPO POGT POGE = POGE
orPO POGT POGT = POGT   -- idempotent

orPO _    _    = POAny

-- | Chains (transitivity) @x R y S z@.
--
--   @seqPO@ is associative, commutative, and idempotent.
--   @seqPO@ has dominant element @POAny@ and neutral element (unit) @POEQ@.

seqPO :: PartialOrdering -> PartialOrdering -> PartialOrdering

seqPO POAny _   = POAny  -- Shortcut if no information on first.
seqPO POEQ p    = p      -- No need to look at second if first is neutral.

seqPO POLT POLT = POLT   -- idempotent
seqPO POLT POLE = POLT
seqPO POLT POEQ = POLT   -- unit

seqPO POLE POLT = POLT
seqPO POLE POLE = POLE   -- idempotent
seqPO POLE POEQ = POLE   -- unit

seqPO POGE POEQ = POGE   -- unit
seqPO POGE POGE = POGE   -- idempotent
seqPO POGE POGT = POGT

seqPO POGT POEQ = POGT   -- unit
seqPO POGT POGE = POGT
seqPO POGT POGT = POGT   -- idempotent

seqPO _    _    = POAny

-- | Partial ordering forms a monoid under sequencing.
instance Semigroup PartialOrdering where
  (<>) = seqPO

instance Monoid PartialOrdering where
  mempty  = POEQ
  mappend = (<>)

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
related a o b = comparable a b `leqPO` o

-- * Totally ordered types.

instance PartialOrd Int where
  comparable = comparableOrd

instance PartialOrd Integer where
  comparable = comparableOrd

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
    (Left  _, Right _) -> POAny
    (Right _, Left  _) -> POAny
    (Right x, Right y) -> comparable x y

-- | Pointwise partial ordering for tuples.
--
--   @related (x1,x2) o (y1,y2)@ iff @related x1 o x2@ and @related y1 o y2@.

instance (PartialOrd a, PartialOrd b) => PartialOrd (a, b) where
  comparable (x1, x2) (y1, y2) =
    comparable x1 y1 `orPO`
    comparable x2 y2

-- | Pointwise comparison wrapper.

newtype Pointwise a = Pointwise { pointwise :: a }
  deriving (Eq, Show, Functor)

-- | The pointwise ordering for lists of the same length.
--
--   There are other partial orderings for lists,
--   e.g., prefix, sublist, subset, lexicographic, simultaneous order.

instance PartialOrd a => PartialOrd (Pointwise [a]) where
  comparable (Pointwise xs) (Pointwise ys) = loop Nothing xs ys
    -- We need an accumulator since @orPO@ does not have a neutral element.
    where
      loop mo []     []     = fromMaybe POEQ mo
      loop _  []     ys     = POAny
      loop _  xs     []     = POAny
      loop mo (x:xs) (y:ys) =
        let o = comparable x y in
        case maybe o (orPO o) mo of
          POAny -> POAny
          o     -> loop (Just o) xs ys

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
