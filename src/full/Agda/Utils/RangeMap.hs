-- | Maps containing non-overlapping intervals.

module Agda.Utils.RangeMap
  ( IsBasicRangeMap(..)
  , several
  , PairInt(..)
  , RangeMap(..)
  , rangeMapInvariant
  , fromNonOverlappingNonEmptyAscendingList
  , insert
  , splitAt
  , insideAndOutside
  , restrictTo
  )
  where

import Prelude hiding (null, splitAt)

import Control.DeepSeq

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Data.Semigroup

import Data.Strict.Tuple (Pair(..))

import Agda.Interaction.Highlighting.Range
import Agda.Utils.List
import Agda.Utils.Null

------------------------------------------------------------------------
-- An abstraction

-- | A class that is intended to make it easy to swap between
-- different range map implementations.
--
-- Note that some 'RangeMap' operations are not included in this
-- class.

class IsBasicRangeMap a m | m -> a where

  -- | The map @'singleton' rs x@ contains the ranges from @rs@, and
  -- every position in those ranges is associated with @x@.

  singleton :: Ranges -> a -> m

  -- | Converts range maps to 'IntMap's from positions to values.

  toMap :: m -> IntMap a

  -- | Converts the map to a list. The ranges are non-overlapping and
  -- non-empty, and earlier ranges precede later ones in the list.

  toList :: m -> [(Range, a)]

  -- | Returns the smallest range covering everything in the map (or
  -- 'Nothing', if the range would be empty).
  --
  -- Note that the default implementation of this operation might be
  -- inefficient.

  coveringRange :: m -> Maybe Range
  coveringRange f = do
    min <- fst <$> IntMap.lookupMin m
    max <- fst <$> IntMap.lookupMax m
    return (Range { from = min, to = max + 1 })
    where
    m = toMap f

-- | Like 'singleton', but with several 'Ranges' instead of only one.

several ::
  (IsBasicRangeMap a hl, Monoid hl) =>
  [Ranges] -> a -> hl
several rss m = mconcat $ map (flip singleton m) rss

------------------------------------------------------------------------
-- A strict pair type

-- | A strict pair type where the first argument must be an 'Int'.
--
-- This type is included because there is no 'NFData' instance for
-- 'Pair' in the package @strict@ before version 4.

newtype PairInt a = PairInt (Pair Int a)
  deriving Show

instance NFData a => NFData (PairInt a) where
  rnf (PairInt (_ :!: y)) = rnf y

-- | Constructs a pair.

pair :: Int -> a -> PairInt a
pair x y = PairInt (x :!: y)

------------------------------------------------------------------------
-- The type

-- | Maps containing non-overlapping intervals.
--
-- The implementation does not use IntMap, because IntMap does not
-- come with a constant-time size function.
--
-- Note the invariant which 'RangeMap's should satisfy
-- ('rangeMapInvariant').

newtype RangeMap a = RangeMap
  { rangeMap :: Map Int (PairInt a)
    -- ^ The keys are starting points of ranges, and the pairs contain
    -- endpoints and values.
  }
  deriving (Show, NFData)

-- | Invariant for 'RangeMap'.
--
-- The ranges must not be empty, and they must not overlap.

rangeMapInvariant :: RangeMap a -> Bool
rangeMapInvariant f = and
  [ all rangeInvariant rs
  , all (not . null) rs
  , caseList rs True $ \ r rs' ->
      and $ zipWith (<=) (map to $ init1 r rs') (map from rs')
  ]
  where
  rs = map fst $ toList f

------------------------------------------------------------------------
-- Construction, conversion and inspection

instance Null (RangeMap a) where
  empty = RangeMap { rangeMap = Map.empty }
  null  = Map.null . rangeMap

instance IsBasicRangeMap a (RangeMap a) where
  singleton (Ranges rs) m =
    RangeMap { rangeMap = Map.fromDistinctAscList rms }
    where
    rms =
      [ (from r, pair (to r) m)
      | r <- rs
      , not (null r)
      ]

  toMap f =
    IntMap.fromList
      [ (p, m)
      | (r, m) <- toList f
      , p <- rangeToPositions r
      ]

  toList =
    map (\(f, PairInt (t :!: a)) -> (Range { from = f, to = t } , a)) .
    Map.toAscList .
    rangeMap

  coveringRange f = do
    min <- fst <$> Map.lookupMin (rangeMap f)
    max <- (\(_, PairInt (p :!: _)) -> p) <$> Map.lookupMax (rangeMap f)
    return (Range { from = min, to = max })

-- | Converts a list of pairs of ranges and values to a 'RangeMap'.
-- The ranges have to be non-overlapping and non-empty, and earlier
-- ranges have to precede later ones.

fromNonOverlappingNonEmptyAscendingList :: [(Range, a)] -> RangeMap a
fromNonOverlappingNonEmptyAscendingList =
  RangeMap .
  Map.fromDistinctAscList .
  map (\(r, m) -> (from r, pair (to r) m))

-- | The number of ranges in the map.
--
-- This function should not be exported.

size :: RangeMap a -> Int
size = Map.size . rangeMap

------------------------------------------------------------------------
-- Merging

-- | Inserts a value, along with a corresponding 'Range', into a
-- 'RangeMap'. No attempt is made to merge adjacent ranges with equal
-- values.
--
-- The function argument is used to combine values. The inserted value
-- is given as the first argument to the function.

insert :: (a -> a -> a) -> Range -> a -> RangeMap a -> RangeMap a
insert combine r m (RangeMap f)
  | null r    = RangeMap f
  | otherwise =
    case equal of
      Just (PairInt (p :!: m')) ->
        case compare (to r) p of
          EQ ->
            -- The range r matches exactly.
            RangeMap $
            Map.insert (from r) (pair p (combine m m')) f
          LT ->
            -- The range r is strictly shorter.
            RangeMap $
            Map.insert (to r) (pair p m') $
            Map.insert (from r) (pair (to r) (combine m m')) f
          GT ->
            -- The range r is strictly longer. Continue recursively.
            insert combine (Range { from = p, to = to r }) m $
            RangeMap $
            Map.insert (from r) (pair p (combine m m')) f
      Nothing ->
        -- Find the part of r that does not overlap with anything in
        -- smaller or larger, if any.
        case (overlapLeft, overlapRight) of
          (Nothing, Nothing) ->
            -- No overlap.
            RangeMap $
            Map.insert (from r) (pair (to r) m) f
          (Nothing, Just p) ->
            -- Overlap on the right. Continue recursively.
            insert combine (Range { from = p, to = to r }) m $
            RangeMap $
            Map.insert (from r) (pair p m) f
          (Just (p1, PairInt (p2 :!: m')), Just p3) ->
            -- Overlap on both sides. Continue recursively.
            insert combine (Range { from = p3, to = to r }) m $
            RangeMap $
            (if p2 == p3 then
               -- The left range ends exactly where the right range
               -- starts.
               id
             else
               -- There is something between the left and right
               -- ranges.
               Map.insert p2 (pair p3 m)) $
            Map.insert (from r) (pair p2 (combine m m')) $
            Map.insert p1 (pair (from r) m') f
          (Just (p1, PairInt (p2 :!: m')), Nothing) ->
            case compare p2 (to r) of
              LT ->
                -- Overlap on the left, the left range ends before r.
                RangeMap $
                Map.insert p2 (pair (to r) m) $
                Map.insert (from r) (pair p2 (combine m m')) $
                Map.insert p1 (pair (from r) m') f
              EQ ->
                -- Overlap on the left, the left range ends where r
                -- ends.
                RangeMap $
                Map.insert (from r) (pair (to r) (combine m m')) $
                Map.insert p1 (pair (from r) m') f
              GT ->
                -- Overlap on the left, the left range ends after r.
                RangeMap $
                Map.insert (to r) (pair p2 m') $
                Map.insert (from r) (pair (to r) (combine m m')) $
                Map.insert p1 (pair (from r) m') f
    where
    (smaller, equal, larger) = Map.splitLookup (from r) f

    overlapRight = case Map.lookupMin larger of
      Nothing -> Nothing
      Just (from, _)
        | from < to r -> Just from
        | otherwise   -> Nothing

    overlapLeft = case Map.lookupMax smaller of
      Nothing -> Nothing
      Just s@(_, PairInt (to :!: _))
        | from r < to -> Just s
        | otherwise   -> Nothing

-- | Merges 'RangeMap's by inserting every \"piece\" of the smaller
-- one into the larger one.

instance Semigroup a => Semigroup (RangeMap a) where
  f1 <> f2
    | size f1 <= size f2 =
      foldr (uncurry $ insert (<>)) f2 (toList f1)
    | otherwise =
      foldr (uncurry $ insert (flip (<>))) f1 (toList f2)

-- | Merges 'RangeMap's by inserting every \"piece\" of the smaller
-- one into the larger one.

instance Semigroup a => Monoid (RangeMap a) where
  mempty  = empty
  mappend = (<>)

------------------------------------------------------------------------
-- Splitting

-- | The value of @'splitAt' p f@ is a pair @(f1, f2)@ which contains
-- everything from @f@. All the positions in @f1@ are less than @p@,
-- and all the positions in @f2@ are greater than or equal to @p@.

splitAt :: Int -> RangeMap a -> (RangeMap a, RangeMap a)
splitAt p f = (before, after)
  where
  (before, _, after) = splitAt' p f

-- | A variant of 'splitAt'. If a range in the middle was split into
-- two pieces, then those two pieces are returned.

splitAt' ::
  Int -> RangeMap a ->
  ( RangeMap a
  , Maybe ((Int, PairInt a), (Int, PairInt a))
  , RangeMap a
  )
splitAt' p (RangeMap f) =
  case equal of
    Just r  -> ( RangeMap maybeOverlapping
               , Nothing
               , RangeMap (Map.insert p r larger)
               )
    Nothing ->
      -- Check if maybeOverlapping overlaps with p.
      case Map.maxViewWithKey maybeOverlapping of
        Nothing ->
          (empty, Nothing, RangeMap larger)
        Just ((from, PairInt (to :!: m)), smaller)
          | to <= p ->
            ( RangeMap maybeOverlapping
            , Nothing
            , RangeMap larger
            )
          | otherwise ->
            -- Here from < p < to.
            ( RangeMap (Map.insert from (pair p m) smaller)
            , Just ((from, pair p m), (p, pair to m))
            , RangeMap (Map.insert p (pair to m) larger)
            )
  where
  (maybeOverlapping, equal, larger) = Map.splitLookup p f

-- | Returns a 'RangeMap' overlapping the given range, as well as the
-- rest of the map.

insideAndOutside :: Range -> RangeMap a -> (RangeMap a, RangeMap a)
insideAndOutside r f
  | from r == to r = (empty, f)
  | otherwise      =
    ( middle
    , -- Because it takes so long to recompile Agda with all
      -- optimisations and run a benchmark no experimental
      -- verification has been made that the code below is better than
      -- reasonable variants. Perhaps it would make sense to benchmark
      -- RangeMap independently of Agda.
      if size before < size middle || size after < size middle then
        RangeMap $ Map.union (rangeMap before) (rangeMap after)
      else
        -- If the number of pieces in the middle is "small", remove
        -- the pieces from f instead of merging before and after.
        RangeMap $
        maybe id (uncurry Map.insert . snd) split1 $
        maybe id (uncurry Map.insert . fst) split2 $
        Map.difference (rangeMap f) (rangeMap middle)
    )
  where
  (beforeMiddle, split1, after) = splitAt' (to r) f
  (before, split2, middle)      = splitAt' (from r) beforeMiddle

-- | Restricts the 'RangeMap' to the given range.

restrictTo :: Range -> RangeMap a -> RangeMap a
restrictTo r = fst . insideAndOutside r
