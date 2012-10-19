{-# LANGUAGE CPP, DeriveDataTypeable, DeriveFunctor, FlexibleInstances, ScopedTypeVariables #-}

{-| Position information for syntax. Crucial for giving good error messages.
-}

module Agda.Syntax.Position
  ( -- * Positions
    Position
  , Position'(..)
  , positionInvariant
  , startPos
  , movePos
  , movePosByString
  , backupPos

    -- * Intervals
  , Interval
  , Interval'(..)
  , intervalInvariant
  , takeI
  , dropI

    -- * Ranges
  , Range
  , Range'(..)
  , rangeInvariant
  , noRange
  , posToRange
  , rStart
  , rEnd
  , rangeToInterval
  , continuous
  , continuousPerLine
  , HasRange(..)
  , SetRange(..)
  , KillRange(..)
  , killRange1, killRange2, killRange3, killRange4, killRange5, killRange6, killRange7
  , withRangeOf
  , fuseRange
  , fuseRanges
  , beginningOf
  , beginningOfFile

    -- * Tests
  , tests
  ) where

import Data.Typeable (Typeable)
import Data.List
import Data.Function
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Data.Int
import Agda.Utils.QuickCheck
import Control.Applicative
import Control.Monad
import Agda.Utils.FileName hiding (tests)
import Agda.Utils.TestHelpers

#include "../undefined.h"
import Agda.Utils.Impossible

{--------------------------------------------------------------------------
    Types and classes
 --------------------------------------------------------------------------}

-- | Represents a point in the input.
--
-- If two positions have the same 'srcFile' and 'posPos' components,
-- then the final two components should be the same as well, but since
-- this can be hard to enforce the program should not rely too much on
-- the last two components; they are mainly there to improve error
-- messages for the user.
--
-- Note the invariant which positions have to satisfy: 'positionInvariant'.
data Position' a = Pn
  { srcFile :: a
    -- ^ File.
  , posPos  :: !Int32
    -- ^ Position.
  , posLine :: !Int32
    -- ^ Line number, counting from 1.
  , posCol  :: !Int32
    -- ^ Column number, counting from 1.
  }
    deriving (Typeable, Functor)

type SrcFile  = Maybe AbsolutePath
type Position = Position' SrcFile

positionInvariant :: Position -> Bool
positionInvariant p =
  posPos p > 0 && posLine p > 0 && posCol p > 0

importantPart p = (srcFile p, posPos p)

instance Eq a => Eq (Position' a) where
  (==) = (==) `on` importantPart

instance Ord a => Ord (Position' a) where
  compare = compare `on` importantPart

-- | An interval. The @iEnd@ position is not included in the interval.
--
-- Note the invariant which intervals have to satisfy: 'intervalInvariant'.
data Interval' a = Interval { iStart, iEnd :: !(Position' a) }
    deriving (Typeable, Eq, Ord, Functor)

type Interval = Interval' SrcFile

intervalInvariant :: Interval -> Bool
intervalInvariant i =
  all positionInvariant [iStart i, iEnd i] &&
  iStart i <= iEnd i

-- | The length of an interval, assuming that the start and end
-- positions are in the same file.
iLength :: Interval -> Int32
iLength i = posPos (iEnd i) - posPos (iStart i)

-- | A range is a list of intervals. The intervals should be
-- consecutive and separated.
--
-- Note the invariant which ranges have to satisfy: 'rangeInvariant'.
newtype Range' a = Range [Interval' a]
  deriving (Typeable, Eq, Ord, Functor)

type Range = Range' SrcFile

rangeInvariant :: Range -> Bool
rangeInvariant (Range []) = True
rangeInvariant (Range is) =
  all intervalInvariant is &&
  and (zipWith (<) (map iEnd $ init is) (map iStart $ tail is))

-- | Things that have a range are instances of this class.
class HasRange t where
    getRange :: t -> Range

instance HasRange Interval where
    getRange i = Range [i]

instance HasRange Range where
    getRange = id

instance HasRange a => HasRange [a] where
    getRange = foldr fuseRange noRange

instance (HasRange a, HasRange b) => HasRange (a,b) where
    getRange = uncurry fuseRange

instance (HasRange a, HasRange b, HasRange c) => HasRange (a,b,c) where
    getRange (x,y,z) = getRange (x,(y,z))

instance (HasRange a, HasRange b, HasRange c, HasRange d) => HasRange (a,b,c,d) where
    getRange (x,y,z,w) = getRange (x,(y,(z,w)))

instance (HasRange a, HasRange b, HasRange c, HasRange d, HasRange e) => HasRange (a,b,c,d,e) where
    getRange (x,y,z,w,v) = getRange (x,(y,(z,(w,v))))

instance (HasRange a, HasRange b, HasRange c, HasRange d, HasRange e, HasRange f) => HasRange (a,b,c,d,e,f) where
    getRange (x,y,z,w,v,u) = getRange (x,(y,(z,(w,(v,u)))))

instance (HasRange a, HasRange b, HasRange c, HasRange d, HasRange e, HasRange f, HasRange g) => HasRange (a,b,c,d,e,f,g) where
    getRange (x,y,z,w,v,u,t) = getRange (x,(y,(z,(w,(v,(u,t))))))

instance HasRange a => HasRange (Maybe a) where
    getRange Nothing  = noRange
    getRange (Just a) = getRange a

-- | If it is also possible to set the range, this is the class.
--
--   Instances should satisfy @'getRange' ('setRange' r x) == r@.
class HasRange t => SetRange t where
  setRange :: Range -> t -> t

instance SetRange Range where
  setRange = const

-- | Killing the range of an object sets all range information to 'noRange'.
class KillRange a where
  killRange :: a -> a

killRange1 f a = f (killRange a)
killRange2 f a = killRange1 (f $ killRange a)
killRange3 f a = killRange2 (f $ killRange a)
killRange4 f a = killRange3 (f $ killRange a)
killRange5 f a = killRange4 (f $ killRange a)
killRange6 f a = killRange5 (f $ killRange a)
killRange7 f a = killRange6 (f $ killRange a)

instance KillRange Range where
  killRange _ = noRange

instance KillRange a => KillRange [a] where
  killRange = map killRange

instance (KillRange a, KillRange b) => KillRange (a, b) where
  killRange (x, y) = (killRange x, killRange y)

instance (KillRange a, KillRange b, KillRange c) =>
         KillRange (a, b, c) where
  killRange (x, y, z) = killRange3 (,,) x y z

instance KillRange a => KillRange (Maybe a) where
  killRange = fmap killRange

instance (KillRange a, KillRange b) => KillRange (Either a b) where
  killRange (Left  x) = Left  $ killRange x
  killRange (Right x) = Right $ killRange x

{--------------------------------------------------------------------------
    Pretty printing
 --------------------------------------------------------------------------}

instance Show a => Show (Position' (Maybe a)) where
    show (Pn Nothing  _ l c) = show l ++ "," ++ show c
    show (Pn (Just f) _ l c) = show f ++ ":" ++ show l ++ "," ++ show c

instance Show a => Show (Interval' (Maybe a)) where
    show (Interval s e) = file ++ start ++ "-" ++ end
	where
	    f	= srcFile s
	    sl	= posLine s
	    el	= posLine e
	    sc	= posCol s
	    ec	= posCol e
	    file = case f of
                     Nothing -> ""
                     Just f  -> show f ++ ":"
	    start = show sl ++ "," ++ show sc
	    end
		| sl == el  = show ec
		| otherwise = show el ++ "," ++ show ec

instance Show a => Show (Range' (Maybe a)) where
  show r = case rangeToInterval r of
    Nothing -> ""
    Just i  -> show i

{--------------------------------------------------------------------------
    Functions on postitions and ranges
 --------------------------------------------------------------------------}

-- | The first position in a file: position 1, line 1, column 1.
startPos :: Maybe AbsolutePath -> Position
startPos f = Pn { srcFile = f, posPos = 1, posLine = 1, posCol = 1 }

-- | Ranges between two unknown positions
noRange :: Range
noRange = Range []

-- | Advance the position by one character.
--   A newline character (@'\n'@) moves the position to the first
--   character in the next line. Any other character moves the
--   position to the next column.
movePos :: Position -> Char -> Position
movePos (Pn f p l c) '\n' = Pn f (p + 1) (l + 1) 1
movePos (Pn f p l c) _	  = Pn f (p + 1) l (c + 1)

-- | Advance the position by a string.
--
--   > movePosByString = foldl' movePos
movePosByString :: Position -> String -> Position
movePosByString = foldl' movePos

-- | Backup the position by one character.
--
-- Precondition: The character must not be @'\n'@.
backupPos :: Position -> Position
backupPos (Pn f p l c) = Pn f (p - 1) l (c - 1)

-- | Extracts the interval corresponding to the given string, assuming
-- that the string starts at the beginning of the given interval.
--
-- Precondition: The string must not be too long for the interval.
takeI :: String -> Interval -> Interval
takeI s i | genericLength s > iLength i = __IMPOSSIBLE__
          | otherwise = i { iEnd = movePosByString (iStart i) s }

-- | Removes the interval corresponding to the given string from the
-- given interval, assuming that the string starts at the beginning of
-- the interval.
--
-- Precondition: The string must not be too long for the interval.
dropI :: String -> Interval -> Interval
dropI s i | genericLength s > iLength i = __IMPOSSIBLE__
          | otherwise = i { iStart = movePosByString (iStart i) s }

-- | Converts two positions to a range.
posToRange :: Position -> Position -> Range
posToRange p1 p2 | p1 < p2   = Range [Interval p1 p2]
                 | otherwise = Range [Interval p2 p1]

-- | Converts a range to an interval, if possible.
rangeToInterval :: Range' a -> Maybe (Interval' a)
rangeToInterval (Range [])   = Nothing
rangeToInterval (Range is)   = Just $ Interval { iStart = iStart (head is)
                                               , iEnd   = iEnd   (last is)
                                               }

-- | Returns the shortest continuous range containing the given one.
continuous :: Range -> Range
continuous r = case rangeToInterval r of
  Nothing -> Range []
  Just i  -> Range [i]

-- | Removes gaps between intervals on the same line.
continuousPerLine :: Range -> Range
continuousPerLine (Range [])     = Range []
continuousPerLine (Range (i:is)) = Range $ fuse i is
  where
    fuse i [] = [i]
    fuse i (j:is)
      | sameLine i j = fuse (fuseIntervals i j) is
      | otherwise    = i : fuse j is
    sameLine i j = posLine (iEnd i) == posLine (iStart j)

-- | The initial position in the range, if any.
rStart :: Range -> Maybe Position
rStart r = iStart <$> rangeToInterval r

-- | The position after the final position in the range, if any.
rEnd :: Range -> Maybe Position
rEnd r = iEnd <$> rangeToInterval r

-- | Finds the least interval which covers the arguments.
fuseIntervals :: Interval -> Interval -> Interval
fuseIntervals x y = Interval { iStart = head ps, iEnd = last ps }
    where ps = sort [iStart x, iStart y, iEnd x, iEnd y]

-- | @fuseRanges r r'@ unions the ranges @r@ and @r'@.
--
--   Meaning it finds the least range @r0@ that covers @r@ and @r'@.
fuseRanges :: Range -> Range -> Range
fuseRanges (Range is) (Range js) = Range (helper is js)
  where
  helper []     js  = js
  helper is     []  = is
  helper (i:is) (j:js)
    | iEnd i < iStart j = i : helper is     (j:js)
    | iEnd j < iStart i = j : helper (i:is) js
    | iEnd i < iEnd j   = helper is (fuseIntervals i j : js)
    | otherwise         = helper (fuseIntervals i j : is) js

fuseRange :: (HasRange u, HasRange t) => u -> t -> Range
fuseRange x y = fuseRanges (getRange x) (getRange y)

-- | @beginningOf r@ is an empty range (a single, empty interval)
-- positioned at the beginning of @r@. If @r@ does not have a
-- beginning, then 'noRange' is returned.
beginningOf :: Range -> Range
beginningOf r = case rStart r of
  Nothing  -> noRange
  Just pos -> posToRange pos pos

-- | @beginningOfFile r@ is an empty range (a single, empty interval)
-- at the beginning of @r@'s starting position's file. If there is no
-- such position, then an empty range is returned.
beginningOfFile :: Range -> Range
beginningOfFile r = case rStart r of
  Nothing                   -> noRange
  Just (Pn { srcFile = f }) -> posToRange p p
    where p = startPos f

-- | @x \`withRangeOf\` y@ sets the range of @x@ to the range of @y@.
withRangeOf :: (SetRange t, HasRange u) => t -> u -> t
x `withRangeOf` y = setRange (getRange y) x

------------------------------------------------------------------------
-- Test suite

-- | The positions corresponding to the interval, /including/ the
-- end-point. This function assumes that the two end points belong to
-- the same file. Note that the 'Arbitrary' instance for 'Position's
-- uses a single, hard-wired file name.
iPositions :: Interval -> Set Int32
iPositions i = Set.fromList [posPos (iStart i) .. posPos (iEnd i)]

-- | The positions corresponding to the range, including the
-- end-points. All ranges are assumed to belong to a single file.
rPositions :: Range -> Set Int32
rPositions (Range is) = Set.unions (map iPositions is)

-- | Constructs the least interval containing all the elements in the
-- set.
makeInterval :: Set Int32 -> Set Int32
makeInterval s
  | Set.null s = Set.empty
  | otherwise  = Set.fromList [Set.findMin s .. Set.findMax s]

prop_iLength i = iLength i >= 0

prop_startPos = positionInvariant . startPos

prop_noRange = rangeInvariant noRange

prop_takeI_dropI i =
  forAll (choose (0, toInteger $ iLength i)) $ \n ->
    let s = genericReplicate n ' '
        t = takeI s i
        d = dropI s i
    in
    intervalInvariant t &&
    intervalInvariant d &&
    fuseIntervals t d == i

prop_rangeToInterval (Range []) = True
prop_rangeToInterval r =
  intervalInvariant i &&
  iPositions i == makeInterval (rPositions r)
  where Just i = rangeToInterval r

prop_continuous r =
  rangeInvariant cr &&
  rPositions cr == makeInterval (rPositions r)
  where cr = continuous r

prop_fuseIntervals i1 =
  forAll (intervalInSameFileAs i1) $ \i2 ->
    let i = fuseIntervals i1 i2 in
    intervalInvariant i &&
    iPositions i ==
      makeInterval (Set.union (iPositions i1) (iPositions i2))

prop_fuseRanges :: Range -> Range -> Bool
prop_fuseRanges r1 r2 =
  rangeInvariant r &&
  rPositions r == Set.union (rPositions r1) (rPositions r2)
  where r = fuseRanges r1 r2

prop_beginningOf r = rangeInvariant (beginningOf r)

prop_beginningOfFile r = rangeInvariant (beginningOfFile r)

instance Arbitrary a => Arbitrary (Position' a) where
  arbitrary = do
    srcFile                    <- arbitrary
    NonZero (NonNegative pos') <- arbitrary
    let pos  = fromInteger pos'
        line = pred pos `div` 10 + 1
        col  = pred pos `mod` 10 + 1
    return (Pn {srcFile = srcFile, posPos = pos,
                posLine = line, posCol = col })

-- | Sets the 'srcFile' components of the interval.

setFile :: SrcFile -> Interval -> Interval
setFile f (Interval p1 p2) =
  Interval (p1 { srcFile = f }) (p2 { srcFile = f })

-- | Generates an interval located in the same file as the given
-- interval.

intervalInSameFileAs i = setFile (srcFile $ iStart i) <$> arbitrary

prop_intervalInSameFileAs i =
  forAll (intervalInSameFileAs i) $ \i' ->
    intervalInvariant i' &&
    srcFile (iStart i) == srcFile (iStart i')

instance (Arbitrary a, Ord a) => Arbitrary (Interval' a) where
  arbitrary = do
    (p1, p2 :: Position' a) <- liftM2 (,) arbitrary arbitrary
    let [p1', p2'] = sort [p1, p2 { srcFile = srcFile p1 }]
    return (Interval p1' p2')

instance Arbitrary Range where
  arbitrary = Range . fuse . sort . fixFiles <$> arbitrary
    where
    fixFiles []       = []
    fixFiles (i : is) = i : map (setFile $ srcFile $ iStart i) is

    fuse (i1 : i2 : is)
      | iEnd i1 >= iStart i2 = fuse (fuseIntervals i1 i2 : is)
      | otherwise            = i1 : fuse (i2 : is)
    fuse is = is

-- | Test suite.
tests :: IO Bool
tests = runTests "Agda.Syntax.Position"
  [ quickCheck' positionInvariant
  , quickCheck' intervalInvariant
  , quickCheck' rangeInvariant
  , quickCheck' prop_iLength
  , quickCheck' prop_startPos
  , quickCheck' prop_noRange
  , quickCheck' prop_takeI_dropI
  , quickCheck' prop_rangeToInterval
  , quickCheck' prop_continuous
  , quickCheck' prop_fuseIntervals
  , quickCheck' prop_fuseRanges
  , quickCheck' prop_beginningOf
  , quickCheck' prop_beginningOfFile
  , quickCheck' prop_intervalInSameFileAs
  ]
