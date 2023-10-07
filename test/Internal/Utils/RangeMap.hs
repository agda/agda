{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.RangeMap
  ( tests
  , overlaps
  , toListProperty
  , coveringRangeProperty
  )
  where

import Prelude hiding (null, splitAt)

import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Semigroup
import Data.Strict.Tuple (Pair(..))

import Agda.Interaction.Highlighting.Range
import Agda.Utils.List (allConsecutive)
import Agda.Utils.Null
import Agda.Utils.RangeMap
import Agda.Utils.Tuple

import Internal.Helpers
import Internal.Interaction.Highlighting.Range ()

------------------------------------------------------------------------
-- Helper definitions

-- | If the two ranges are defined and overlap, then the test case is
-- classified as \"overlapping\".

overlaps :: Testable p => Maybe Range -> Maybe Range -> p -> Property
overlaps r1 r2 =
  classify
    (maybe False (maybe (const False) overlapping r1) r2)
    "overlapping"

-- | Classifies test cases based on whether the intersection of the
-- range and the 'RangeMap' is non-empty, and whether any range in the
-- internal representation of the 'RangeMap' is \"split\" by the given
-- range: to the left, to the right, or on both sides.

intersectsSplits :: Testable p => Range -> RangeMap a -> p -> Property
intersectsSplits r f =
  classify (not (null inside))             "non-empty intersection" .
  classify (rangeContainingPoint (from r)) "split to the left" .
  classify (rangeContainingPoint (to r))   "split to the right" .
  classify rangeContainingRange            "one range split twice"
  where
  (inside, outside) = insideAndOutside r f

  -- Is there a range that contains the given point, but not as the
  -- starting point? In that case the range's endpoint is returned.
  rangeContainingPoint' p = case Map.splitLookup p (rangeMap f) of
    (_,       Just _,  _) -> Nothing
    (smaller, Nothing, _) -> case Map.lookupMax smaller of
      Just (p1, PairInt (p2 :!: _))
        | p1 < p && p < p2 -> Just p2
      _                    -> Nothing

  -- Is there a range that contains the given point, but not as the
  -- starting point?
  rangeContainingPoint = isJust . rangeContainingPoint'

  -- Is there a range that contains the range r, starts before r, and
  -- ends after r?
  rangeContainingRange = case rangeContainingPoint' (from r) of
    Nothing  -> False
    Just end -> to r < end

-- | A property that should be satisfied by 'toList'.

toListProperty :: (Eq a, IsBasicRangeMap a m) => m -> Bool
toListProperty f =
  all (not . null) rs
    &&
  increasing rs
    &&
  toMap f ==
  IntMap.fromList [ (p, m) | (r, m) <- rms, p <- rangeToPositions r ]
  where
  rms = toList f
  rs  = map fst rms
  increasing = allConsecutive \ r r' -> to r <= from r'

-- | A property that should be satisfied by 'coveringRange'.

coveringRangeProperty :: IsBasicRangeMap a m => m -> Bool
coveringRangeProperty f =
  coveringRange f ==
  do from <- fst <$> IntMap.lookupMin (toMap f)
     to   <- fst <$> IntMap.lookupMax (toMap f)
     return (Range { from = from, to = to + 1 })

-- | A type synonym used for some tests below.

type RangeMap' = RangeMap [Int]

-- | A variant of 'RangeMap'' with an 'Eq' instance.

newtype RangeMap'Eq = RangeMap'Eq RangeMap'
  deriving (Arbitrary, Semigroup, Monoid, Show)

instance Eq RangeMap'Eq where
  RangeMap'Eq f1 == RangeMap'Eq f2 = toMap f1 == toMap f2

------------------------------------------------------------------------
-- Invariants

prop_rangeMapInvariant1 :: RangeMap' -> Bool
prop_rangeMapInvariant1 = rangeMapInvariant

prop_rangeMapInvariant2 :: RangeMap' -> Bool
prop_rangeMapInvariant2 = all rangeMapInvariant . shrink

prop_rangeMapInvariant3 :: [Ranges] -> [Int] -> Bool
prop_rangeMapInvariant3 rs m =
  rangeMapInvariant $ several (take 5 rs) m

prop_rangeMapInvariant4 :: Ranges -> [Int] -> Bool
prop_rangeMapInvariant4 r m = rangeMapInvariant $ singleton r m

prop_rangeMapInvariant5 :: [(Range, [Int])] -> Bool
prop_rangeMapInvariant5 rs =
  rangeMapInvariant $ fromNonOverlappingNonEmptyAscendingList rs'
  where
  rs' =
    increasing $
    filter (not . null . fst) rs

  increasing (r1 : r2 : rs)
    | to (fst r1) <= from (fst r2) = r1 : increasing (r2 : rs)
    | otherwise                    = increasing (r1 : rs)
  increasing rs = rs

prop_rangeMapInvariant6 ::
  ([Int] -> [Int] -> [Int]) ->
  Range -> [Int] -> RangeMap' -> Property
prop_rangeMapInvariant6 g r m f =
  overlaps (Just r) (coveringRange f) $
  rangeMapInvariant $ insert g r m f

prop_rangeMapInvariant7 :: RangeMap' -> RangeMap' -> Property
prop_rangeMapInvariant7 f1 f2 =
  overlaps (coveringRange f1) (coveringRange f2) $
  rangeMapInvariant $ f1 <> f2

prop_rangeMapInvariant8 :: Int -> RangeMap' -> Property
prop_rangeMapInvariant8 p f =
  overlaps (Just (Range { from = p, to = p + 1 })) (coveringRange f) $
  all rangeMapInvariant $ (\(f1, f2) -> [f1, f2]) $
  splitAt p f

prop_rangeMapInvariant9 :: Range -> RangeMap' -> Property
prop_rangeMapInvariant9 r f =
  overlaps (Just r) (coveringRange f) $
  all rangeMapInvariant $ (\(f1, f2) -> [f1, f2]) $
  insideAndOutside r f

-- | A property that is intended to exercise the else branch in
-- 'insideAndOutside'.

prop_rangeMapInvariant10 :: RangeMap' -> Property
prop_rangeMapInvariant10 f =
  forAll (rangeInside f) $ \r ->
  intersectsSplits r f $
  all rangeMapInvariant $ (\(f1, f2) -> [f1, f2]) $
  insideAndOutside r f

prop_rangeMapInvariant11 :: Range -> RangeMap' -> Property
prop_rangeMapInvariant11 r f =
  overlaps (Just r) (coveringRange f) $
  rangeMapInvariant $ restrictTo r f

prop_rangeInvariant1 :: RangeMap' -> Bool
prop_rangeInvariant1 f = all (rangeInvariant . fst) (toList f)

prop_rangeInvariant2 :: RangeMap' -> Bool
prop_rangeInvariant2 = maybe True rangeInvariant . coveringRange

prop_rangeInvariant3 :: RangeMap' -> Property
prop_rangeInvariant3 f = forAll (rangeInside f) rangeInvariant

------------------------------------------------------------------------
-- Operations

prop_several :: [Ranges] -> [Int] -> Bool
prop_several rss' m =
  toMap (several rss m :: RangeMap') ==
  IntMap.fromListWith (flip (<>))
    [ (p, m)
    | rs <- rss
    , p  <- rangesToPositions rs
    ]
  where
  rss = take 5 rss'

prop_empty :: Bool
prop_empty = toMap (empty :: RangeMap') == IntMap.empty

prop_null :: RangeMap' -> Bool
prop_null f = null f == IntMap.null (toMap f)

prop_singleton :: Ranges -> [Int] -> Bool
prop_singleton rs m =
  toMap (singleton rs m :: RangeMap') ==
  IntMap.fromList
    [ (p, m)
    | p <- rangesToPositions rs
    ]

prop_toList :: RangeMap' -> Bool
prop_toList = toListProperty

prop_coveringRange :: RangeMap' -> Bool
prop_coveringRange = coveringRangeProperty

prop_fromNonOverlappingNonEmptyAscendingList_toList :: RangeMap' -> Bool
prop_fromNonOverlappingNonEmptyAscendingList_toList f =
  toMap (fromNonOverlappingNonEmptyAscendingList (toList f)) ==
  toMap f

prop_insert ::
  ([Int] -> [Int] -> [Int]) ->
  Range -> [Int] -> RangeMap' -> Property
prop_insert g r m f =
  overlaps (Just r) (coveringRange f) $
  toMap (insert g r m f) ==
  IntMap.unionWith
    g
    (IntMap.fromList [ (p, m) | p <- rangeToPositions r ])
    (toMap f)

prop_append :: RangeMap' -> RangeMap' -> Property
prop_append f1 f2 =
  overlaps (coveringRange f1) (coveringRange f2) $
  toMap (f1 <> f2) ==
  IntMap.unionWith mappend (toMap f1) (toMap f2)

prop_splitAt :: Int -> RangeMap' -> Property
prop_splitAt p f =
  overlaps (Just (Range { from = p, to = p + 1 })) (coveringRange f) $
  all (<  p) (positions f1) &&
  all (>= p) (positions f2) &&
  toMap (f1 <> f2) == toMap f
  where
  (f1, f2) = splitAt p f

  positions = IntMap.keys . toMap

prop_insideAndOutside1 :: Range -> RangeMap' -> Property
prop_insideAndOutside1 r f =
  overlaps (Just r) (coveringRange f) $
  toMap inside == IntMap.restrictKeys (toMap f) positions
    &&
  toMap outside == IntMap.withoutKeys (toMap f) positions
  where
  (inside, outside) = insideAndOutside r f
  positions         = IntSet.fromList $ rangeToPositions r

-- | A property that is intended to exercise the else branch in
-- 'insideAndOutside'.

prop_insideAndOutside2 :: RangeMap' -> Property
prop_insideAndOutside2 f =
  forAll (rangeInside f) $ \r ->
  intersectsSplits r f $
  prop_insideAndOutside1 r f

prop_restrictTo :: Range -> RangeMap' -> Property
prop_restrictTo r f =
  overlaps (Just r) (coveringRange f) $
  toMap (restrictTo r f) ==
  IntMap.restrictKeys (toMap f) (IntSet.fromList (rangeToPositions r))

------------------------------------------------------------------------
-- Algebraic properties

-- | 'RangeMap'Eq' is a monoid.

prop_monoid :: Property3 RangeMap'Eq
prop_monoid = isMonoid

------------------------------------------------------------------------
-- Generators

instance (Arbitrary a, Semigroup a) => Arbitrary (RangeMap a) where
  arbitrary = smaller 5 $ do
    rs <- (\ns1 ns2 ->
            toRanges $ sort $
            ns1 ++ concatMap (\n -> [n, succ n]) (ns2 :: [Int])) <$>
            arbitrary <*> arbitrary
    RangeMap . Map.fromList <$>
      mapM (\r -> (\m -> (from r, PairInt (to r :!: m))) <$> arbitrary)
        rs
    where
    toRanges (f : t : rs)
      | f == t    = toRanges (t : rs)
      | otherwise = Range { from = f, to = t } :
                    toRanges (case rs of
                                f : rs | t == f -> rs
                                _               -> rs)
    toRanges _ = []

  shrink f =
    [ RangeMap (Map.deleteAt i (rangeMap f))
    | i <- [0 .. Map.size (rangeMap f) - 1]
    ] ++
    [ RangeMap (Map.updateAt (\_ _ -> Just (PairInt (p :!: x)))
                  i (rangeMap f))
    | i <- [0 .. Map.size (rangeMap f) - 1]
    , let (_, PairInt (p :!: x)) = Map.elemAt i (rangeMap f)
    , x <- shrink x
    ]

instance CoArbitrary a => CoArbitrary (RangeMap a) where
  coarbitrary (RangeMap f) =
    coarbitrary $
    fmap (mapSnd (\(PairInt (x :!: y)) -> (x, y))) $
    Map.toAscList f

-- | A range that is entirely inside a given 'RangeMap'.

rangeInside :: RangeMap a -> Gen Range
rangeInside f =
  case coveringRange f of
    Nothing -> return (Range { from = 0, to = 0 })
    Just r  -> oneof
      [ do
        low  <- chooseInt (from r, to r)
        high <- chooseInt (low, to r)
        return (Range { from = low, to = high })
      , do
        high <- chooseInt (from r, to r)
        low  <- chooseInt (from r, high)
        return (Range { from = low, to = high })
      ]

prop_rangeInside :: RangeMap' -> Property
prop_rangeInside f =
  forAll (rangeInside f) $ \r ->
  case coveringRange f of
    Nothing -> from r == to r
    Just r' -> from r' <= from r && to r <= to r'

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
tests = testProperties "Internal.Utils.RangeMap" $allProperties
