{-# LANGUAGE TemplateHaskell #-}

module Internal.Syntax.Position ( tests ) where

import Agda.Syntax.Position
import Agda.Syntax.TopLevelModuleName
import Agda.Utils.FileName
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.List ( distinct )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Null ( null )

import Control.Monad

import Data.Int
import Data.List (sort)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as T

import Internal.Helpers
import Internal.Syntax.Common ()
import Internal.Utils.FileName (rootPath)
import Internal.Utils.Maybe.Strict ()

import Prelude hiding ( null )

import System.FilePath

------------------------------------------------------------------------
-- Test suite

-- | The positions corresponding to the interval. The positions do not
-- refer to characters, but to the positions between characters, with
-- zero pointing to the position before the first character.
iPositions :: Interval' a -> Set Int32
iPositions i = Set.fromList [posPos (iStart i) .. posPos (iEnd i)]

-- | The positions corresponding to the range, including the
-- end-points.
rPositions :: Range' a -> Set Int32
rPositions r = Set.unions (map iPositions $ rangeIntervals r)

-- | Constructs the least interval containing all the elements in the
-- set.
makeInterval :: Set Int32 -> Set Int32
makeInterval s
  | Set.null s = Set.empty
  | otherwise  = Set.fromList [Set.findMin s .. Set.findMax s]

prop_iLength :: Interval' Integer -> Bool
prop_iLength i = iLength i >= 0

prop_startPos' :: Bool
prop_startPos' = positionInvariant (startPos' ())

prop_startPos :: Maybe RangeFile -> Bool
prop_startPos = positionInvariant . startPos

prop_noRange :: Bool
prop_noRange = rangeInvariant (noRange :: Range)

prop_posToRange' ::
  Integer -> PositionWithoutFile -> PositionWithoutFile -> Bool
prop_posToRange' f p1 p2 =
  rangeInvariant (posToRange' f p1 p2)

prop_posToRange :: Position' Integer -> Position' Integer -> Bool
prop_posToRange p1 p2 =
  rangeInvariant (posToRange p1 (p2 { srcFile = srcFile p1 }))

prop_intervalToRange :: Integer -> IntervalWithoutFile -> Bool
prop_intervalToRange f i = rangeInvariant (intervalToRange f i)

rangeToIntervalPropertyTemplate ::
  Ord a =>
  (Range' Integer -> Maybe (Interval' a)) ->
  Range' Integer -> Bool
rangeToIntervalPropertyTemplate r2i r = case r2i r of
  Nothing -> r == noRange
  Just i  ->
    r /= noRange
      &&
    intervalInvariant i
      &&
    iPositions i == makeInterval (rPositions r)

prop_rangeToIntervalWithFile :: Range' Integer -> Bool
prop_rangeToIntervalWithFile =
  rangeToIntervalPropertyTemplate rangeToIntervalWithFile

prop_rangeToInterval :: Range' Integer -> Bool
prop_rangeToInterval =
  rangeToIntervalPropertyTemplate rangeToInterval

prop_continuous :: Range -> Bool
prop_continuous r =
  rangeInvariant cr &&
  rPositions cr == makeInterval (rPositions r)
  where cr = continuous r

prop_continuousPerLine :: Range -> Bool
prop_continuousPerLine r =
  rangeInvariant r'
    &&
  distinct lineNumbers
    &&
  rangeFile r' == rangeFile r
  where
  r' = continuousPerLine r

  lineNumbers = concatMap lines (rangeIntervals r')
    where
    lines i | s == e    = [s]
            | otherwise = [s, e]
      where
      s = posLine (iStart i)
      e = posLine (iEnd   i)

prop_fuseIntervals :: Interval' Integer -> Property
prop_fuseIntervals i1 =
  forAll (intervalInSameFileAs i1) $ \i2 ->
    let i = fuseIntervals i1 i2 in
    intervalInvariant i &&
    iPositions i ==
      makeInterval (Set.union (iPositions i1) (iPositions i2))

prop_fuseRanges :: Range -> Property
prop_fuseRanges r1 =
  forAll (rangeInSameFileAs r1) $ \r2 ->
    let r = fuseRanges r1 r2 in
    rangeInvariant r
      &&
    rPositions r == Set.union (rPositions r1) (rPositions r2)

prop_beginningOf :: Range -> Bool
prop_beginningOf r = rangeInvariant (beginningOf r)

prop_beginningOfFile :: Range -> Bool
prop_beginningOfFile r = rangeInvariant (beginningOfFile r)

instance Arbitrary a => Arbitrary (Position' a) where
  arbitrary = do
    srcFile       <- arbitrary
    Positive pos' <- arbitrary
    let pos  = fromInteger pos'
        line = pred pos `div` 10 + 1
        col  = pred pos `mod` 10 + 1
    return (Pn {srcFile = srcFile, posPos = pos,
                posLine = line, posCol = col })

-- | Generates an interval located in the same file as the given
-- interval.

intervalInSameFileAs ::
  (Arbitrary a, Ord a) => Interval' a -> Gen (Interval' a)
intervalInSameFileAs i =
  setIntervalFile (srcFile $ iStart i) <$>
    (arbitrary :: Gen IntervalWithoutFile)

prop_intervalInSameFileAs :: Interval' Integer -> Property
prop_intervalInSameFileAs i =
  forAll (intervalInSameFileAs i) $ \i' ->
    intervalInvariant i' &&
    srcFile (iStart i) == srcFile (iStart i')

-- | Generates a range located in the same file as the given
-- range (if possible).

rangeInSameFileAs :: (Arbitrary a, Ord a) => Range' a -> Gen (Range' a)
rangeInSameFileAs NoRange      = arbitrary
rangeInSameFileAs (Range f is) = do
  Range _f is <- arbitrary `suchThat` (not . null)
  return $ Range (f `asTypeOf` _f) is

prop_rangeInSameFileAs :: Range' Integer -> Property
prop_rangeInSameFileAs r =
  forAll (rangeInSameFileAs r) $ \r' ->
    rangeInvariant r'
      &&
    case (r, r') of
      (NoRange, _)            -> True
      (Range f _, Range f' _) -> f == f'
      (Range _ _, NoRange)    -> False

instance Arbitrary RawTopLevelModuleName where
  arbitrary = do
    r     <- arbitrary
    parts <- list1Of (T.pack <$> listOf1 (elements "AB"))
    return $ RawTopLevelModuleName
      { rawModuleNameRange = r
      , rawModuleNameParts = parts
      }

instance Arbitrary TopLevelModuleName where
  arbitrary = do
    raw <- arbitrary
    return $
      unsafeTopLevelModuleName raw
        (hashRawTopLevelModuleName raw)

instance CoArbitrary TopLevelModuleName where
  coarbitrary = coarbitrary . moduleNameId

instance Arbitrary RangeFile where
  arbitrary = do
    top   <- arbitrary
    extra <- take 2 . map (take 2) <$> listOf (listOf1 (elements "a1"))
    let f = mkAbsolute $ joinPath $
            rootPath : extra ++
            map T.unpack (List1.toList (moduleNameParts top))
    return $ mkRangeFile f (Just top)

instance (Arbitrary a, Ord a) => Arbitrary (Interval' a) where
  arbitrary = do
    (p1, p2 :: Position' a) <- liftM2 (,) arbitrary arbitrary
    let [p1', p2'] = sort [p1, p2 { srcFile = srcFile p1 }]
    return (Interval p1' p2')

instance (Ord a, Arbitrary a) => Arbitrary (Range' a) where
  arbitrary = do
    f <- arbitrary
    intervalsToRange f . fuse . sort <$> arbitrary
    where
    fuse (i1 : i2 : is)
      | iEnd i1 >= iStart i2 = fuse (fuseIntervals i1 i2 : is)
      | otherwise            = i1 : fuse (i2 : is)
    fuse is = is

instance CoArbitrary RangeFile
instance CoArbitrary a => CoArbitrary (Position' a)
instance CoArbitrary a => CoArbitrary (Interval' a)
instance CoArbitrary a => CoArbitrary (Range' a)

prop_positionInvariant :: Position' Integer -> Bool
prop_positionInvariant = positionInvariant

prop_intervalInvariant :: Interval' Integer -> Bool
prop_intervalInvariant = intervalInvariant

prop_rangeInvariant :: Range -> Bool
prop_rangeInvariant = rangeInvariant

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
tests = testProperties "Internal.Syntax.Position" $allProperties
