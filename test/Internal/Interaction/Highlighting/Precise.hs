{-# LANGUAGE TemplateHaskell #-}

module Internal.Interaction.Highlighting.Precise ( tests ) where

import Agda.Interaction.Highlighting.Precise as P
import Agda.Interaction.Highlighting.Range
import Agda.Utils.Null
import Agda.Utils.RangeMap (RangeMap, rangeMapInvariant)
import qualified Agda.Utils.RangeMap as RangeMap

import Prelude hiding (null, splitAt)

import Control.Monad

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Semigroup (Endo(..), (<>))

import Internal.Helpers
import Internal.Interaction.Highlighting.Range ()
import Internal.Syntax.Common ()
import Internal.Syntax.Concrete.Name ()
import Internal.Utils.RangeMap hiding (tests)

------------------------------------------------------------------------
-- A helper function

-- | This function is used to construct counterexamples.

simpleMap :: IsBasicRangeMap Aspects m => Aspect -> m
simpleMap a = singleton
  (Ranges [Range { from = 1, to = 2 }])
  (mempty { aspect = Just a })

------------------------------------------------------------------------
-- Invariants

prop_rangePairInvariant1 :: RangePair -> Bool
prop_rangePairInvariant1 = rangePairInvariant

prop_rangePairInvariant2 :: RangePair -> Bool
prop_rangePairInvariant2 = all rangePairInvariant . shrink

prop_rangePairInvariant3 :: Ranges -> Aspects -> Bool
prop_rangePairInvariant3 r m = rangePairInvariant $ singleton r m

prop_rangeMapDMInvariant1 :: DelayedMerge (RangeMap Aspects) -> Bool
prop_rangeMapDMInvariant1 =
  delayedMergeInvariant rangeMapInvariant

prop_rangeMapDMInvariant2 :: DelayedMerge (RangeMap Aspects) -> Bool
prop_rangeMapDMInvariant2 =
  all (delayedMergeInvariant rangeMapInvariant) . take 5 . shrink

prop_rangeMapDMInvariant3 :: Ranges -> Aspects -> Bool
prop_rangeMapDMInvariant3 r m =
  delayedMergeInvariant rangeMapInvariant $ singleton r m

prop_rangeMapDMInvariant4 :: [Ranges] -> Aspects -> Bool
prop_rangeMapDMInvariant4 rs m =
  delayedMergeInvariant rangeMapInvariant $ several (take 5 rs) m

prop_rangeMapDMInvariant5 ::
  DelayedMerge (RangeMap Aspects) -> DelayedMerge (RangeMap Aspects) ->
  Property
prop_rangeMapDMInvariant5 f1 f2 =
  overlaps (coveringRange f1) (coveringRange f2) $
  delayedMergeInvariant rangeMapInvariant $ f1 <> f2

prop_rangePairDMInvariant1 :: DelayedMerge RangePair -> Bool
prop_rangePairDMInvariant1 =
  delayedMergeInvariant rangePairInvariant

prop_rangePairDMInvariant2 :: DelayedMerge RangePair -> Bool
prop_rangePairDMInvariant2 =
  all (delayedMergeInvariant rangePairInvariant) . take 5 . shrink

prop_rangePairDMInvariant3 :: Ranges -> Aspects -> Bool
prop_rangePairDMInvariant3 r m =
  delayedMergeInvariant rangePairInvariant $ singleton r m

prop_rangePairDMInvariant4 :: [Ranges] -> Aspects -> Bool
prop_rangePairDMInvariant4 rs m =
  delayedMergeInvariant rangePairInvariant $ several (take 5 rs) m

prop_rangePairDMInvariant5 ::
  DelayedMerge RangePair -> DelayedMerge RangePair -> Property
prop_rangePairDMInvariant5 f1 f2 =
  overlaps (coveringRange f1) (coveringRange f2) $
  delayedMergeInvariant rangePairInvariant $ f1 <> f2

prop_rangeInvariant1 :: RangePair -> Bool
prop_rangeInvariant1 f = all (rangeInvariant . fst) (toList f)

prop_rangeInvariant2 :: RangePair -> Bool
prop_rangeInvariant2 = maybe True rangeInvariant . coveringRange

prop_rangeInvariant3 :: PositionMap -> Bool
prop_rangeInvariant3 f = all (rangeInvariant . fst) (toList f)

prop_rangeInvariant4 :: PositionMap -> Bool
prop_rangeInvariant4 = maybe True rangeInvariant . coveringRange

prop_rangeInvariant5 :: DelayedMerge (RangeMap Aspects) -> Bool
prop_rangeInvariant5 f = all (rangeInvariant . fst) (toList f)

prop_rangeInvariant6 :: DelayedMerge (RangeMap Aspects) -> Bool
prop_rangeInvariant6 = maybe True rangeInvariant . coveringRange

prop_rangeInvariant7 :: DelayedMerge RangePair -> Bool
prop_rangeInvariant7 f = all (rangeInvariant . fst) (toList f)

prop_rangeInvariant8 :: DelayedMerge RangePair -> Bool
prop_rangeInvariant8 = maybe True rangeInvariant . coveringRange

prop_rangeInvariant9 :: DelayedMerge PositionMap -> Bool
prop_rangeInvariant9 f = all (rangeInvariant . fst) (toList f)

prop_rangeInvariant10 :: DelayedMerge PositionMap -> Bool
prop_rangeInvariant10 = maybe True rangeInvariant . coveringRange

------------------------------------------------------------------------
-- RangePair operations

prop_singletonRP :: Ranges -> Aspects -> Bool
prop_singletonRP rs m =
  toMap (singleton rs m :: RangePair) ==
  IntMap.fromList
    [ (p, m)
    | p <- rangesToPositions rs
    ]

prop_toListRP :: RangePair -> Bool
prop_toListRP = toListProperty

prop_coveringRangeRP :: RangePair -> Bool
prop_coveringRangeRP = coveringRangeProperty

------------------------------------------------------------------------
-- PositionMap operations

prop_memptyPM :: Bool
prop_memptyPM = toMap (mempty :: PositionMap) == IntMap.empty

prop_singletonPM :: Ranges -> Aspects -> Bool
prop_singletonPM rs m =
  toMap (singleton rs m :: PositionMap) ==
  IntMap.fromList
    [ (p, m)
    | p <- rangesToPositions rs
    ]

prop_severalPM :: [Ranges] -> Aspects -> Bool
prop_severalPM rss' m =
  toMap (several rss m :: PositionMap) ==
  IntMap.fromListWith (flip (<>))
    [ (p, m)
    | rs <- rss
    , p  <- rangesToPositions rs
    ]
  where
  rss = take 5 rss'

prop_toListPM :: PositionMap -> Bool
prop_toListPM = toListProperty

prop_coveringRangePM :: PositionMap -> Bool
prop_coveringRangePM = coveringRangeProperty

prop_appendPM :: PositionMap -> PositionMap -> Property
prop_appendPM f1 f2 =
  overlaps (coveringRange f1) (coveringRange f2) $
  toMap (f1 <> f2) ==
  IntMap.unionWith mappend (toMap f1) (toMap f2)

------------------------------------------------------------------------
-- Operations for DelayedMerge (RangeMap Aspects)

prop_memptyDMRM :: Bool
prop_memptyDMRM =
  toMap (mempty :: DelayedMerge (RangeMap Aspects)) == IntMap.empty

prop_singletonDMRM :: Ranges -> Aspects -> Bool
prop_singletonDMRM rs m =
  toMap (singleton rs m :: DelayedMerge (RangeMap Aspects)) ==
  IntMap.fromList
    [ (p, m)
    | p <- rangesToPositions rs
    ]

prop_severalDMRM :: [Ranges] -> Aspects -> Bool
prop_severalDMRM rss' m =
  toMap (several rss m :: DelayedMerge (RangeMap Aspects)) ==
  IntMap.fromListWith (flip (<>))
    [ (p, m)
    | rs <- rss
    , p  <- rangesToPositions rs
    ]
  where
  rss = take 5 rss'

prop_toListDMRM :: DelayedMerge (RangeMap Aspects) -> Bool
prop_toListDMRM = toListProperty

prop_coveringRangeDMRM :: DelayedMerge (RangeMap Aspects) -> Bool
prop_coveringRangeDMRM = coveringRangeProperty

prop_appendDMRM ::
  DelayedMerge (RangeMap String) -> DelayedMerge (RangeMap String) ->
  Property
prop_appendDMRM f1 f2 =
  overlaps (coveringRange f1) (coveringRange f2) $
  toMap (f1 <> f2) ==
  IntMap.unionWith mappend (toMap f1) (toMap f2)

------------------------------------------------------------------------
-- Operations for DelayedMerge RangePair

prop_memptyDMRP :: Bool
prop_memptyDMRP =
  toMap (mempty :: DelayedMerge RangePair) == IntMap.empty

prop_singletonDMRP :: Ranges -> Aspects -> Bool
prop_singletonDMRP rs m =
  toMap (singleton rs m :: DelayedMerge RangePair) ==
  IntMap.fromList
    [ (p, m)
    | p <- rangesToPositions rs
    ]

prop_severalDMRP :: [Ranges] -> Aspects -> Bool
prop_severalDMRP rss' m =
  toMap (several rss m :: DelayedMerge RangePair) ==
  IntMap.fromListWith (flip (<>))
    [ (p, m)
    | rs <- rss
    , p  <- rangesToPositions rs
    ]
  where
  rss = take 5 rss'

-- | The following property does not hold, because 'mappend' is not
-- associative for 'Aspects'. It might hold for \"compatible\" pieces
-- of @'DelayedMerge' 'RangePair'@.

not_prop_toListDMRP :: DelayedMerge RangePair -> Bool
not_prop_toListDMRP = toListProperty

-- | A counterexample to 'not_prop_toListDMRP'.

prop_counterexample_to_prop_toListDMRP :: Bool
prop_counterexample_to_prop_toListDMRP =
  not (not_prop_toListDMRP f)
  where
  f = DelayedMerge $ Endo
    ([ simpleMap (Name Nothing True)
     , simpleMap Keyword
     , simpleMap (Name (Just Datatype) True)
     ] ++)

prop_coveringRangeDMRP :: DelayedMerge RangePair -> Bool
prop_coveringRangeDMRP = coveringRangeProperty

-- | The following property does not hold, because 'mappend' is not
-- associative for 'Aspects'. It might hold for \"compatible\" pieces
-- of @'DelayedMerge' 'RangePair'@.

not_prop_appendDMRP ::
  DelayedMerge RangePair -> DelayedMerge RangePair -> Bool
not_prop_appendDMRP f1 f2 =
  toMap (f1 <> f2) ==
  IntMap.unionWith mappend (toMap f1) (toMap f2)

-- | A counterexample to 'not_prop_appendDMRP'.

prop_counterexample_to_prop_appendDMRP :: Bool
prop_counterexample_to_prop_appendDMRP =
  not (not_prop_appendDMRP f1 f2)
  where
  f1 = DelayedMerge $ Endo
    ([ simpleMap (Name Nothing True)
     ] ++)

  f2 = DelayedMerge $ Endo
    ([ simpleMap Keyword
     , simpleMap (Name (Just Datatype) True)
     ] ++)

------------------------------------------------------------------------
-- Operations for DelayedMerge PositionMap

prop_memptyDMPM :: Bool
prop_memptyDMPM =
  toMap (mempty :: DelayedMerge PositionMap) == IntMap.empty

prop_singletonDMPM :: Ranges -> Aspects -> Bool
prop_singletonDMPM rs m =
  toMap (singleton rs m :: DelayedMerge PositionMap) ==
  IntMap.fromList
    [ (p, m)
    | p <- rangesToPositions rs
    ]

prop_severalDMPM :: [Ranges] -> Aspects -> Bool
prop_severalDMPM rss' m =
  toMap (several rss m :: DelayedMerge PositionMap) ==
  IntMap.fromListWith (flip (<>))
    [ (p, m)
    | rs <- rss
    , p  <- rangesToPositions rs
    ]
  where
  rss = take 5 rss'

prop_toListDMPM :: DelayedMerge PositionMap -> Bool
prop_toListDMPM = toListProperty

prop_coveringRangeDMPM :: DelayedMerge PositionMap -> Bool
prop_coveringRangeDMPM = coveringRangeProperty

-- | The following property does not hold, because 'mappend' is not
-- associative for 'Aspects'. It might hold for \"compatible\" pieces
-- of @'DelayedMerge' 'PositionMap'@.

not_prop_appendDMPM ::
  DelayedMerge PositionMap -> DelayedMerge PositionMap -> Bool
not_prop_appendDMPM f1 f2 =
  toMap (f1 <> f2) ==
  IntMap.unionWith mappend (toMap f1) (toMap f2)

-- | A counterexample to 'not_prop_appendDMPM'.

prop_counterexample_to_prop_appendDMPM :: Bool
prop_counterexample_to_prop_appendDMPM =
  not (not_prop_appendDMPM f1 f2)
  where
  f1 = DelayedMerge $ Endo
    ([ simpleMap (Name Nothing True)
     , simpleMap Keyword
     ] ++)

  f2 = DelayedMerge $ Endo
    ([ simpleMap (Name (Just Datatype) True)
     ] ++)

------------------------------------------------------------------------
-- Conversions

prop_convertDMRM :: DelayedMerge (RangeMap Aspects) -> Bool
prop_convertDMRM f = toMap f == toMap (convert f :: RangeMap Aspects)

prop_convertDMPM :: DelayedMerge PositionMap -> Bool
prop_convertDMPM f = toMap f == toMap (convert f :: PositionMap)

prop_convertRMRM :: RangeMap Aspects -> Bool
prop_convertRMRM f = toMap f == toMap (convert f :: RangeMap Aspects)

prop_convertPMRM :: PositionMap -> Bool
prop_convertPMRM f = toMap f == toMap (convert f :: RangeMap Aspects)

prop_convertDMPMRM :: DelayedMerge PositionMap -> Bool
prop_convertDMPMRM f = toMap f == toMap (convert f :: RangeMap Aspects)

prop_convertDMRPPM :: DelayedMerge RangePair -> Bool
prop_convertDMRPPM f = toMap f == toMap (convert f :: PositionMap)

-- | The following property does not hold, because 'mappend' is not
-- associative for 'Aspects'. It might hold for \"compatible\" pieces
-- of @'DelayedMerge' 'RangePair'@.

not_prop_convertDMRPRM :: DelayedMerge RangePair -> Bool
not_prop_convertDMRPRM f = toMap f == toMap (convert f :: RangeMap Aspects)

-- | A counterexample to 'not_prop_convertDMRPRM'.

prop_counterexample_to_prop_convertDMRPRM :: Bool
prop_counterexample_to_prop_convertDMRPRM =
  not (not_prop_convertDMRPRM f)
  where
  f = DelayedMerge $ Endo
    ([ simpleMap (Name Nothing True)
     , simpleMap Keyword
     , simpleMap (Name (Just Datatype) True)
     ] ++)

------------------------------------------------------------------------
-- Algebraic properties

-- Andreas, 2020-04-13:  Deactived these (trivial) tests for monoidality.
--
-- NameKind is no longer associative.  Composition used to be just the left
-- projection, but now Field dominates over Bound.
--
--   (Bound <> Macro) <> Field = Bound <> Field = Field
--   Bound <> (Macro <> Field) = Bound <> Macro = Bound
--
-- Straightforward associativity for all triples is ignoring the fact
-- that many such triples do not arise in practice.
-- In fact, NameKind is rather a partial order where some analyses give
-- more precise kinds than others.
--
-- -- | 'Aspects' is a monoid.
-- prop_monoid_Aspects :: Property3 Aspects
-- prop_monoid_Aspects = isMonoid

-- -- | 'HighlightingInfo' is a monoid.
-- prop_monoid_HighlightingInfo :: Property3 HighlightingInfo
-- prop_monoid_HighlightingInfo = isMonoid

-- -- | 'HighlightingInfoBuilder' is a monoid.
-- prop_monoid_HighlightingInfoBuilder ::
--   Property3 HighlightingInfoBuilder
-- prop_monoid_HighlightingInfoBuilder = isMonoid

------------------------------------------------------------------------
-- Generators

instance Arbitrary Aspect where
  arbitrary =
    frequency [ (3, elements [ Comment, Keyword, String, Number
                             , Symbol, PrimitiveType, Pragma ])
              , (1, liftM2 Name (maybeGen arbitrary) arbitrary)
              ]

  shrink Name{} = [Comment]
  shrink _      = []

instance CoArbitrary Aspect where
  coarbitrary Comment       = variant 0
  coarbitrary Keyword       = variant 1
  coarbitrary String        = variant 2
  coarbitrary Number        = variant 3
  coarbitrary Symbol        = variant 4
  coarbitrary PrimitiveType = variant 5
  coarbitrary (Name nk b)   =
    variant 6 . maybeCoGen coarbitrary nk . coarbitrary b
  coarbitrary Pragma        = variant 7
  coarbitrary Background    = variant 8
  coarbitrary Markup        = variant 9
  coarbitrary Hole          = variant 10

instance Arbitrary NameKind where
  arbitrary = oneof $ [fmap Constructor arbitrary] ++
                      map return [ Bound
                                 , Datatype
                                 , Field
                                 , Function
                                 , Module
                                 , Postulate
                                 , Primitive
                                 , Record
                                 ]

  shrink Constructor{} = [Bound]
  shrink _             = []

instance CoArbitrary NameKind where
  coarbitrary Bound             = variant 0
  coarbitrary (Constructor ind) = variant 1 . coarbitrary ind
  coarbitrary Datatype          = variant 2
  coarbitrary Field             = variant 3
  coarbitrary Function          = variant 4
  coarbitrary Module            = variant 5
  coarbitrary Postulate         = variant 6
  coarbitrary Primitive         = variant 7
  coarbitrary Record            = variant 8
  coarbitrary Argument          = variant 9
  coarbitrary Macro             = variant 10
  coarbitrary Generalizable     = variant 11

instance Arbitrary OtherAspect where
  arbitrary = elements [minBound .. maxBound]

instance CoArbitrary OtherAspect where
  coarbitrary = coarbitrary . fromEnum

instance Arbitrary Aspects where
  arbitrary = do
    aspect     <- arbitrary
    other      <- arbitrary
    note       <- string
    defSite    <- arbitrary
    tokenBased <- arbitrary
    return (Aspects { aspect         = aspect
                    , otherAspects   = other
                    , note           = note
                    , definitionSite = defSite
                    , tokenBased     = tokenBased
                    })
    where string = listOfElements "abcdefABCDEF/\\.\"'@()åäö\n"

  shrink (Aspects a o n d t) =
    [ Aspects a o n d t | a <- shrink a ] ++
    [ Aspects a o n d t | o <- shrink o ] ++
    [ Aspects a o n d t | n <- shrink n ] ++
    [ Aspects a o n d t | d <- shrink d ] ++
    [ Aspects a o n d t | t <- shrink t ]

instance CoArbitrary Aspects where
  coarbitrary (Aspects aspect otherAspects note defSite tokenBased) =
    coarbitrary aspect .
    coarbitrary otherAspects .
    coarbitrary note .
    coarbitrary defSite .
    coarbitrary tokenBased

instance Arbitrary TokenBased where
  arbitrary = elements [TokenBased, NotOnlyTokenBased]

  shrink TokenBased        = [NotOnlyTokenBased]
  shrink NotOnlyTokenBased = []

instance CoArbitrary TokenBased where
  coarbitrary TokenBased        = variant 0
  coarbitrary NotOnlyTokenBased = variant 1

instance Arbitrary DefinitionSite where
  arbitrary = liftM4 DefinitionSite arbitrary arbitrary arbitrary $ maybeGen string
    where string = listOfElements "abcdefABCDEF/\\.'åäö"

  shrink (DefinitionSite a b c d) =
    [ DefinitionSite a b c d | a <- shrink a ] ++
    [ DefinitionSite a b c d | b <- shrink b ] ++
    [ DefinitionSite a b c d | c <- shrink c ] ++
    [ DefinitionSite a b c d | d <- shrink d ]

instance CoArbitrary DefinitionSite where
  coarbitrary (DefinitionSite a b c d) =
    coarbitrary a .
    coarbitrary b .
    coarbitrary c .
    coarbitrary d

instance Arbitrary RangePair where
  arbitrary            = RangePair <$> arbitrary
  shrink (RangePair p) = [ RangePair p | p <- shrink p ]

instance CoArbitrary RangePair where
  coarbitrary (RangePair p) = coarbitrary p

instance Arbitrary PositionMap where
  arbitrary =
    smaller 5 $
    fmap (PositionMap . IntMap.fromList) $
    listOf arbitrary

  shrink =
    map (PositionMap . IntMap.fromList) .
    shrink .
    IntMap.toList .
    positionMap

instance CoArbitrary PositionMap where
  coarbitrary (PositionMap f) = coarbitrary (IntMap.toAscList f)

instance Arbitrary hl => Arbitrary (DelayedMerge hl) where
  arbitrary = DelayedMerge . Endo . (++) . take 10 <$> arbitrary

  shrink (DelayedMerge f) =
    [ DelayedMerge (Endo (f ++))
    | f <- shrink (appEndo f [])
    ]

instance (Arbitrary hl, CoArbitrary hl) =>
         CoArbitrary (DelayedMerge hl) where
  coarbitrary (DelayedMerge f) = coarbitrary f

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
tests = testProperties "Internal.Interaction.Highlighting.Precise" $allProperties
