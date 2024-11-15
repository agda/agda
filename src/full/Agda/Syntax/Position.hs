{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE UndecidableInstances #-} -- Due to KILLRANGE vararg typeclass

{-| Position information for syntax. Crucial for giving good error messages.
-}

module Agda.Syntax.Position
  ( -- * Positions
    Position
  , PositionWithoutFile
  , Position'(..)
  , SrcFile
  , RangeFile(..)
  , mkRangeFile
  , positionInvariant
  , startPos
  , startPos'
  , movePos
  , movePosByString
  , backupPos

    -- * Intervals
  , Interval
  , IntervalWithoutFile
  , Interval'(Interval, iStart', iEnd')
  , intervalInvariant
  , iStart
  , iEnd
  , posToInterval
  , getIntervalFile
  , iLength
  , fuseIntervals

    -- * Ranges
  , Range
  , RangeWithoutFile
  , Range'(..)
  , rangeInvariant
  , consecutiveAndSeparated
  , intervalsToRange
  , intervalToRange
  , rangeFromAbsolutePath
  , rangeIntervals
  , rangeFile
  , rangeModule'
  , rangeModule
  , rightMargin
  , noRange
  , posToRange, posToRange'
  , rStart, rStart'
  , rEnd, rEnd'
  , rangeToInterval
  , rangeToIntervalWithFile
  , continuous
  , continuousPerLine
  , PrintRange(..)
  , HasRange(..)
  , HasRangeWithoutFile(..)
  , SetRange(..)
  , KillRange(..)
  , KillRangeT
  , killRangeMap
  , KILLRANGE(..)
  , withRangeOf
  , fuseRange
  , fuseRanges
  , beginningOf
  , beginningOfFile
  , interleaveRanges
  ) where

import Prelude hiding ( null )

import Control.DeepSeq
import Control.Monad
import Control.Monad.Writer (runWriter, tell)

import qualified Data.Foldable as Fold
import Data.Function (on)
import Data.List (sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Semigroup (Semigroup(..))
import Data.Void
import Data.Word (Word32)

import GHC.Generics (Generic)

import Agda.Syntax.TopLevelModuleName.Boot (TopLevelModuleName'(..))

import Agda.Utils.FileName
import Agda.Utils.List
import Agda.Utils.List1 (List1)
import Agda.Utils.List2 (List2)
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Set1 (Set1)
import qualified Agda.Utils.Set1 as Set1
import Agda.Utils.TypeLevel (IsBase, All, Domains)
import Agda.Utils.Tuple (sortPair)

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
  { srcFile :: !a
    -- ^ File.
  , posPos  :: !Word32
    -- ^ Position, counting from 1.
  , posLine :: !Word32
    -- ^ Line number, counting from 1.
  , posCol  :: !Word32
    -- ^ Column number, counting from 1.
  }
  deriving (Show, Functor, Foldable, Traversable, Generic)

positionInvariant :: Position' a -> Bool
positionInvariant p =
  posPos p > 0 && posLine p > 0 && posCol p > 0

importantPart :: Position' a -> (a, Word32)
importantPart p = (srcFile p, posPos p)

instance Eq a => Eq (Position' a) where
  (==) = (==) `on` importantPart

instance Ord a => Ord (Position' a) where
  compare = compare `on` importantPart

type SrcFile = Strict.Maybe RangeFile

-- | File information used in the 'Position', 'Interval' and 'Range'
-- types.
data RangeFile = RangeFile
  { rangeFilePath :: !AbsolutePath
    -- ^ The file's path.
  , rangeFileName :: !(Maybe (TopLevelModuleName' Range))
    -- ^ The file's top-level module name (if applicable).
    --
    -- This field is optional, but some things may break if the field
    -- is not instantiated with an actual top-level module name. For
    -- instance, the 'Eq' and 'Ord' instances only make use of this
    -- field.
    --
    -- The field uses 'Maybe' rather than 'Strict.Maybe' because it
    -- should be possible to instantiate it with something that is not
    -- yet defined (see 'Agda.Interaction.Imports.parseSource').
    --
    -- This '(TopLevelModuleName' Range)' should not contain a range.
  }
  deriving (Show, Generic)

-- | A smart constructor for 'RangeFile'.

mkRangeFile :: AbsolutePath -> Maybe (TopLevelModuleName' Range) -> RangeFile
mkRangeFile f top = RangeFile
  { rangeFilePath = f
  , rangeFileName = killRange top
  }

-- | Only the 'rangeFileName' component is compared.

instance Eq RangeFile where
  (==) = (==) `on` rangeFileName

-- | Only the 'rangeFileName' component is compared.

instance Ord RangeFile where
  compare = compare `on` rangeFileName

instance NFData RangeFile where
  rnf (RangeFile _ n) = rnf n

type Position            = Position' SrcFile
type PositionWithoutFile = Position' ()

instance NFData Position where
  rnf = (`seq` ())

instance NFData PositionWithoutFile where
  rnf = (`seq` ())

-- | An interval. The @iEnd@ position is not included in the interval.
--
-- Note the invariant which intervals have to satisfy: 'intervalInvariant'.
data Interval' a = Interval
  { getIntervalFile :: a
  , iStart' :: !PositionWithoutFile
  , iEnd'   :: !PositionWithoutFile
  }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)

type Interval            = Interval' SrcFile
type IntervalWithoutFile = Interval' ()

instance NFData Interval where
  rnf = (`seq` ())

instance NFData IntervalWithoutFile where
  rnf = (`seq` ())

intervalInvariant :: Ord a => Interval' a -> Bool
intervalInvariant i = and
  [ positionInvariant $ iStart i
  , positionInvariant $ iEnd i
  , iStart i <= iEnd i
  ]

iStart :: Interval' a -> Position' a
iStart (Interval f s _) = f <$ s

iEnd   :: Interval' a -> Position' a
iEnd   (Interval f _ e) = f <$ e

-- | Converts a file name and two positions to an interval.
--   Sort the positions ascendingly.
posToInterval ::
  a -> PositionWithoutFile -> PositionWithoutFile -> Interval' a
posToInterval f p1 p2 = uncurry (Interval f) $ sortPair (p1, p2)

-- | The length of an interval.
iLength :: Interval' a -> Word32
iLength i = posPos (iEnd i) - posPos (iStart i)

-- | A range is a file name, plus a sequence of intervals, assumed to
-- point to the given file. The intervals should be consecutive and
-- separated.
--
-- Note the invariant which ranges have to satisfy: 'rangeInvariant'.
data Range' a
  = NoRange
  | Range !a (Seq IntervalWithoutFile)
  deriving
    (Show, Eq, Ord, Functor, Foldable, Traversable, Generic)

type Range = Range' SrcFile
type RangeWithoutFile = Range' ()

instance NFData a => NFData (Range' a)

instance Null (Range' a) where
  null NoRange = True
  null Range{} = False

  empty = NoRange

instance Eq a => Semigroup (Range' a) where
  NoRange <> r = r
  r <> NoRange = r
  Range f is <> Range f' is'
    | f /= f'   = __IMPOSSIBLE__
    | otherwise = Range f (is <> is')

instance Eq a => Monoid (Range' a) where
  mempty  = empty
  mappend = (<>)

-- | The intervals that make up the range. The intervals are
-- consecutive and separated ('consecutiveAndSeparated').
rangeIntervals :: Range' a -> [IntervalWithoutFile]
rangeIntervals NoRange      = []
rangeIntervals (Range _ is) = Fold.toList is

-- | Turns a file name plus a list of intervals into a range.
--
-- Precondition: 'consecutiveAndSeparated'.
intervalsToRange :: a -> [IntervalWithoutFile] -> Range' a
intervalsToRange _ [] = NoRange
intervalsToRange f is = Range f (Seq.fromList is)

-- | Are the intervals consecutive and separated, do they all point to
-- the same file, and do they satisfy the interval invariant?
consecutiveAndSeparated :: Ord a => [Interval' a] -> Bool
consecutiveAndSeparated is =
  all intervalInvariant is
    &&
  allEqual (map (srcFile . iStart) is)
    &&
  allConsecutive (\ i j -> iEnd i < iStart j) is

-- | Range invariant.
rangeInvariant :: Ord a => Range' a -> Bool
rangeInvariant r =
  consecutiveAndSeparated (rangeIntervals r)
    &&
  case r of
    Range _ is -> not (null is)
    NoRange    -> True

-- | The file the range is pointing to.
rangeFile :: Range -> SrcFile
rangeFile NoRange     = Strict.Nothing
rangeFile (Range f _) = f

-- | The range's top-level module name, if any.
--
-- If there is no range, then 'Nothing' is returned. If there is a
-- range without a module name, then @'Just' 'Nothing'@ is returned.
rangeModule' :: Range -> Maybe (Maybe (TopLevelModuleName' Range))
rangeModule' NoRange     = Nothing
rangeModule' (Range f _) = Just $ case f of
  Strict.Nothing -> Nothing
  Strict.Just f  -> rangeFileName f

-- | The range's top-level module name, if any.
rangeModule :: Range -> Maybe (TopLevelModuleName' Range)
rangeModule = join . rangeModule'

-- | Conflate a range to its right margin.
rightMargin :: Range -> Range
rightMargin r@NoRange      = r
rightMargin r@(Range f is) = case Seq.viewr is of
  Seq.EmptyR -> __IMPOSSIBLE__
  _ Seq.:> Interval () s e -> intervalToRange f (Interval () e e)

-- | Wrapper to indicate that range should be printed.
newtype PrintRange a = PrintRange a
  deriving (Eq, Ord, HasRange, SetRange, KillRange)

-- | Things that have a range are instances of this class.
class HasRange a where
  getRange :: a -> Range

  default getRange :: (Foldable t, HasRange b, t b ~ a) => a -> Range
  getRange = Fold.foldr fuseRange noRange
  {-# INLINABLE getRange #-}

instance HasRange Interval where
  getRange (Interval f p1 p2) = intervalToRange f (Interval () p1 p2)

instance HasRange Range where
    getRange = id

instance HasRange () where
  getRange _ = noRange

instance HasRange Bool where
    getRange _ = noRange

instance HasRange (TopLevelModuleName' Range) where
  getRange = moduleNameRange

instance SetRange (TopLevelModuleName' Range) where
  setRange r (TopLevelModuleName _ h x) = TopLevelModuleName r h x

instance KillRange (TopLevelModuleName' Range) where
  killRange (TopLevelModuleName _ h x) = TopLevelModuleName noRange h x

-- | Precondition: The ranges of the list elements must point to the
-- same file (or be empty).
instance HasRange a => HasRange [a]

-- | Precondition: The ranges of the list elements must point to the
-- same file (or be empty).
instance HasRange a => HasRange (List1 a)
instance HasRange a => HasRange (List2 a)
instance HasRange a => HasRange (Maybe a)
instance HasRange a => HasRange (Set1 a)

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b) => HasRange (a,b) where
    getRange = uncurry fuseRange

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b, HasRange c) => HasRange (a,b,c) where
    getRange (x,y,z) = getRange (x,(y,z))

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b, HasRange c, HasRange d) => HasRange (a,b,c,d) where
    getRange (x,y,z,w) = getRange (x,(y,(z,w)))

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b, HasRange c, HasRange d, HasRange e) => HasRange (a,b,c,d,e) where
    getRange (x,y,z,w,v) = getRange (x,(y,(z,(w,v))))

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b, HasRange c, HasRange d, HasRange e, HasRange f) => HasRange (a,b,c,d,e,f) where
    getRange (x,y,z,w,v,u) = getRange (x,(y,(z,(w,(v,u)))))

-- | Precondition: The ranges of the tuple elements must point to the
-- same file (or be empty).
instance (HasRange a, HasRange b, HasRange c, HasRange d, HasRange e, HasRange f, HasRange g) => HasRange (a,b,c,d,e,f,g) where
    getRange (x,y,z,w,v,u,t) = getRange (x,(y,(z,(w,(v,(u,t))))))

instance (HasRange a, HasRange b) => HasRange (Either a b) where
    getRange = either getRange getRange

-- | Things that have a 'RangeWithoutFile' are instances of this class.

class HasRangeWithoutFile a where
  getRangeWithoutFile :: a -> RangeWithoutFile

  default getRangeWithoutFile :: (Foldable t, HasRangeWithoutFile b, t b ~ a) => a -> RangeWithoutFile
  getRangeWithoutFile = Fold.foldr fuseRangeWithoutFile noRange
  {-# INLINABLE getRangeWithoutFile #-}

instance HasRangeWithoutFile IntervalWithoutFile where
  getRangeWithoutFile = intervalToRange ()

instance HasRangeWithoutFile RangeWithoutFile where
    getRangeWithoutFile = id

instance HasRangeWithoutFile () where
  getRangeWithoutFile _ = noRange

instance HasRangeWithoutFile Bool where
    getRangeWithoutFile _ = noRange

-- UNUSED:
-- instance HasRangeWithoutFile (TopLevelModuleName' RangeWithoutFile) where
--   getRangeWithoutFile = moduleNameRange

instance HasRangeWithoutFile a => HasRangeWithoutFile [a]
instance HasRangeWithoutFile a => HasRangeWithoutFile (List1 a)
instance HasRangeWithoutFile a => HasRangeWithoutFile (List2 a)
instance HasRangeWithoutFile a => HasRangeWithoutFile (Maybe a)
instance HasRangeWithoutFile a => HasRangeWithoutFile (Set1 a)

instance (HasRangeWithoutFile a, HasRangeWithoutFile b) => HasRangeWithoutFile (a,b) where
    getRangeWithoutFile = uncurry fuseRangeWithoutFile

instance (HasRangeWithoutFile a, HasRangeWithoutFile b, HasRangeWithoutFile c) => HasRangeWithoutFile (a,b,c) where
    getRangeWithoutFile (x,y,z) = getRangeWithoutFile (x,(y,z))

instance (HasRangeWithoutFile a, HasRangeWithoutFile b, HasRangeWithoutFile c, HasRangeWithoutFile d) => HasRangeWithoutFile (a,b,c,d) where
    getRangeWithoutFile (x,y,z,w) = getRangeWithoutFile (x,(y,(z,w)))

instance (HasRangeWithoutFile a, HasRangeWithoutFile b, HasRangeWithoutFile c, HasRangeWithoutFile d, HasRangeWithoutFile e) => HasRangeWithoutFile (a,b,c,d,e) where
    getRangeWithoutFile (x,y,z,w,v) = getRangeWithoutFile (x,(y,(z,(w,v))))

instance (HasRangeWithoutFile a, HasRangeWithoutFile b, HasRangeWithoutFile c, HasRangeWithoutFile d, HasRangeWithoutFile e, HasRangeWithoutFile f) => HasRangeWithoutFile (a,b,c,d,e,f) where
    getRangeWithoutFile (x,y,z,w,v,u) = getRangeWithoutFile (x,(y,(z,(w,(v,u)))))

instance (HasRangeWithoutFile a, HasRangeWithoutFile b, HasRangeWithoutFile c, HasRangeWithoutFile d, HasRangeWithoutFile e, HasRangeWithoutFile f, HasRangeWithoutFile g) => HasRangeWithoutFile (a,b,c,d,e,f,g) where
    getRangeWithoutFile (x,y,z,w,v,u,t) = getRangeWithoutFile (x,(y,(z,(w,(v,(u,t))))))

instance (HasRangeWithoutFile a, HasRangeWithoutFile b) => HasRangeWithoutFile (Either a b) where
    getRangeWithoutFile = either getRangeWithoutFile getRangeWithoutFile

-- | If it is also possible to set the range, this is the class.
--
--   Instances should satisfy @'getRange' ('setRange' r x) == r@.
class HasRange a => SetRange a where
  setRange :: Range -> a -> a

  default setRange :: (Functor f, SetRange b, f b ~ a) => Range -> a -> a
  setRange = fmap . setRange

instance SetRange Range where
  setRange = const

instance SetRange a => SetRange [a]
instance SetRange a => SetRange (Maybe a)

-- | Killing the range of an object sets all range information to 'noRange'.
class KillRange a where
  killRange :: KillRangeT a

  default killRange :: (Functor f, KillRange b, f b ~ a) => KillRangeT a
  killRange = fmap killRange

type KillRangeT a = a -> a

class KILLRANGE t b where
  killRangeN :: IsBase t ~ b => All KillRange (Domains t) =>
                t -> t

instance IsBase t ~ 'True => KILLRANGE t 'True where
  {-# INLINE killRangeN #-}
  killRangeN v = v

instance KILLRANGE t (IsBase t) => KILLRANGE (a -> t) 'False where
  {-# INLINE killRangeN #-}
  killRangeN f a = killRangeN (f (killRange a))

-- | Remove ranges in keys and values of a map.
killRangeMap :: (KillRange k, KillRange v) => KillRangeT (Map k v)
killRangeMap = Map.mapKeysMonotonic killRange . Map.map killRange

instance KillRange Range where
  killRange _ = noRange

instance KillRange Void where
  killRange = id

instance KillRange () where
  killRange = id

instance KillRange Bool where
  killRange = id

instance KillRange Int where
  killRange = id

instance KillRange Integer where
  killRange = id

instance KillRange Permutation where
  killRange = id

-- | Overlaps with @KillRange [a]@.
instance {-# OVERLAPPING #-} KillRange String where
  killRange = id

instance {-# OVERLAPPABLE #-} KillRange a => KillRange [a]
instance {-# OVERLAPPABLE #-} KillRange a => KillRange (Map k a)

instance KillRange a => KillRange (Drop a)
instance KillRange a => KillRange (List1 a)
instance KillRange a => KillRange (List2 a)
instance KillRange a => KillRange (Maybe a)
instance KillRange a => KillRange (Strict.Maybe a)

instance {-# OVERLAPPABLE #-} (Ord a, KillRange a) => KillRange (Set a) where
  killRange = Set.map killRange

instance (Ord a, KillRange a) => KillRange (Set1 a) where
  killRange = Set1.map killRange

instance (KillRange a, KillRange b) => KillRange (a, b) where
  killRange (x, y) = (killRange x, killRange y)

instance (KillRange a, KillRange b, KillRange c) =>
         KillRange (a, b, c) where
  killRange (x, y, z) = killRangeN (,,) x y z

instance (KillRange a, KillRange b, KillRange c, KillRange d) =>
         KillRange (a, b, c, d) where
  killRange (x, y, z, u) = killRangeN (,,,) x y z u

instance (KillRange a, KillRange b) => KillRange (Either a b) where
  killRange (Left  x) = Left  $ killRange x
  killRange (Right x) = Right $ killRange x

{--------------------------------------------------------------------------
    Functions on positions and ranges
 --------------------------------------------------------------------------}

-- | The first position in a file: position 1, line 1, column 1.
startPos' :: a -> Position' a
startPos' f = Pn
  { srcFile = f
  , posPos  = 1
  , posLine = 1
  , posCol  = 1
  }

-- | The first position in a file: position 1, line 1, column 1.
startPos :: Maybe RangeFile -> Position
startPos = startPos' . Strict.toStrict

-- | Range pointing to the first position in the given file.
rangeFromAbsolutePath :: AbsolutePath -> Range
rangeFromAbsolutePath f = posToRange' src p0 p0
  where
    src = Strict.Just $ mkRangeFile f Nothing
    p0  = startPos' ()

-- | Ranges between two unknown positions
noRange :: Range' a
noRange = NoRange

-- | Advance the position by one character.
--   A newline character (@'\n'@) moves the position to the first
--   character in the next line. Any other character moves the
--   position to the next column.
movePos :: Position' a -> Char -> Position' a
movePos (Pn f p l c) '\n' = Pn f (p + 1) (l + 1) 1
movePos (Pn f p l c) _    = Pn f (p + 1) l (c + 1)

-- | Advance the position by a string.
--
--   > movePosByString = foldl' movePos
movePosByString :: Foldable t => Position' a -> t Char -> Position' a
movePosByString = Fold.foldl' movePos

-- | Backup the position by one character.
--
-- Precondition: The character must not be @'\n'@.
backupPos :: Position' a -> Position' a
backupPos (Pn f p l c) = Pn f (p - 1) l (c - 1)

-- | Converts a file name and two positions to a range.
posToRange' ::
  a -> PositionWithoutFile -> PositionWithoutFile -> Range' a
posToRange' f p1 p2 = intervalToRange f (posToInterval () p1 p2)

-- | Converts two positions to a range.
--
-- Precondition: The positions have to point to the same file.
posToRange :: Position' a -> Position' a -> Range' a
posToRange p1 p2 =
  posToRange' (srcFile p1) (p1 { srcFile = () }) (p2 { srcFile = () })

-- | Converts a file name and an interval to a range.
intervalToRange :: a -> IntervalWithoutFile -> Range' a
intervalToRange f i = Range f (Seq.singleton i)

-- | Converts a range to an interval, if possible.
rangeToIntervalWithFile :: Range' a -> Maybe (Interval' a)
rangeToIntervalWithFile NoRange      = Nothing
rangeToIntervalWithFile (Range f is) =
  case (Seq.viewl is, Seq.viewr is) of
    (head Seq.:< _, _ Seq.:> last) -> Just $ Interval f (iStart head) (iEnd last)
    _ -> __IMPOSSIBLE__

-- | Converts a range to an interval, if possible.
-- Note that the information about the source file is lost.
rangeToInterval :: Range' a -> Maybe IntervalWithoutFile
rangeToInterval = rangeToIntervalWithFile . void

-- | Returns the shortest continuous range containing the given one.
continuous :: Range' a -> Range' a
continuous NoRange = NoRange
continuous r@(Range f _) =
  maybe __IMPOSSIBLE__ (intervalToRange f) $ rangeToInterval r

-- | Removes gaps between intervals on the same line.
continuousPerLine :: Ord a => Range' a -> Range' a
continuousPerLine r@NoRange     = r
continuousPerLine r@(Range f _) =
  Range f (Seq.unfoldr step (rangeIntervals r))
  where
  step []  = Nothing
  step [i] = Just (i, [])
  step (i : is@(j : js))
    | sameLine  = step (fuseIntervals i j : js)
    | otherwise = Just (i, is)
    where
    sameLine = posLine (iEnd i) == posLine (iStart j)

-- | The initial position in the range, if any.
rStart' :: Range' a -> Maybe PositionWithoutFile
rStart' r = iStart <$> rangeToInterval r

-- | The initial position in the range, if any.
rStart :: Range' a -> Maybe (Position' a)
rStart NoRange       = Nothing
rStart r@(Range f _) = (\p -> p { srcFile = f }) <$> rStart' r

-- | The position after the final position in the range, if any.
rEnd' :: Range' a -> Maybe PositionWithoutFile
rEnd' r = iEnd <$> rangeToInterval r

-- | The position after the final position in the range, if any.
rEnd :: Range' a -> Maybe (Position' a)
rEnd NoRange       = Nothing
rEnd r@(Range f _) = (\p -> p { srcFile = f }) <$> rEnd' r

-- | Finds the least interval which covers the arguments.
--
fuseIntervals :: IntervalWithoutFile -> IntervalWithoutFile -> IntervalWithoutFile
fuseIntervals (Interval () s1 e1) (Interval () s2 e2) = Interval () (min s1 s2) (max e1 e2)

-- | @fuseRanges r r'@ unions the ranges @r@ and @r'@.
--
--   Meaning it finds the least range @r0@ that covers @r@ and @r'@.
--
-- Precondition: The ranges must point to the same file (or be empty).
fuseRanges :: (Ord a) => Range' a -> Range' a -> Range' a
fuseRanges NoRange       is2           = is2
fuseRanges is1           NoRange       = is1
fuseRanges (Range f is1) (Range _ is2) = Range f (fuse is1 is2)
  where
  fuse is1 is2 = case (Seq.viewl is1, Seq.viewr is1,
                       Seq.viewl is2, Seq.viewr is2) of
    (Seq.EmptyL, _, _, _) -> is2
    (_, _, Seq.EmptyL, _) -> is1
    (s1 Seq.:< r1, l1 Seq.:> e1, s2 Seq.:< r2, l2 Seq.:> e2)
        -- Special cases.
      | iEnd e1 <  iStart s2 -> is1 Seq.>< is2
      | iEnd e2 <  iStart s1 -> is2 Seq.>< is1
      | iEnd e1 == iStart s2 -> mergeTouching l1 e1 s2 r2
      | iEnd e2 == iStart s1 -> mergeTouching l2 e2 s1 r1
        -- General cases.
      | iEnd s1 <  iStart s2 -> outputLeftPrefix s1 r1 s2 is2
      | iEnd s2 <  iStart s1 -> outputLeftPrefix s2 r2 s1 is1
      | iEnd s1 <  iEnd   s2 -> fuseSome s1 r1 s2 r2
      | otherwise            -> fuseSome s2 r2 s1 r1
    _ -> __IMPOSSIBLE__

  mergeTouching l e s r = l Seq.>< i Seq.<| r
    where
    i = Interval () (iStart e) (iEnd s)

  -- The following two functions could use binary search instead of
  -- linear.

  outputLeftPrefix s1 r1 s2 is2 = s1 Seq.<| r1' Seq.>< fuse r1'' is2
    where
    (r1', r1'') = Seq.spanl (\s -> iEnd s < iStart s2) r1

  fuseSome s1 r1 s2 r2 = fuse r1' (fuseIntervals s1 s2 Seq.<| r2)
    where
    r1' = Seq.dropWhileL (\s -> iEnd s <= iEnd s2) r1

{-# INLINE fuseRange #-}
-- | Precondition: The ranges must point to the same file (or be
-- empty).
fuseRange :: (HasRange u, HasRange t) => u -> t -> Range
fuseRange x y = fuseRanges (getRange x) (getRange y)

{-# INLINE fuseRangeWithoutFile #-}
-- | Precondition: The ranges must point to the same file (or be
-- empty).
fuseRangeWithoutFile :: (HasRangeWithoutFile u, HasRangeWithoutFile t) => u -> t -> RangeWithoutFile
fuseRangeWithoutFile x y = fuseRanges (getRangeWithoutFile x) (getRangeWithoutFile y)

-- | @beginningOf r@ is an empty range (a single, empty interval)
-- positioned at the beginning of @r@. If @r@ does not have a
-- beginning, then 'noRange' is returned.
beginningOf :: Range -> Range
beginningOf NoRange       = NoRange
beginningOf r@(Range f _) = case rStart' r of
  Nothing  -> __IMPOSSIBLE__
  Just pos -> posToRange' f pos pos

-- | @beginningOfFile r@ is an empty range (a single, empty interval)
-- at the beginning of @r@'s starting position's file. If there is no
-- such position, then an empty range is returned.
beginningOfFile :: Range -> Range
beginningOfFile NoRange     = NoRange
beginningOfFile (Range f _) = posToRange' f p p
  where p = startPos' ()

-- | @x \`withRangeOf\` y@ sets the range of @x@ to the range of @y@.
withRangeOf :: (SetRange t, HasRange u) => t -> u -> t
x `withRangeOf` y = setRange (getRange y) x

-- | Interleaves two streams of ranged elements
--
--   It will report the conflicts as a list of conflicting pairs.
--   In case of conflict, the element with the earliest start position
--   is placed first. In case of a tie, the element with the earliest
--   ending position is placed first. If both tie, the element from the
--   first list is placed first.
interleaveRanges :: forall a. (HasRangeWithoutFile a) => [a] -> [a] -> ([a], [(a,a)])
interleaveRanges as bs = runWriter $ go as bs
  where
    go []         as = return as
    go as         [] = return as
    go as@(a:as') bs@(b:bs') =
      let ra = getRangeWithoutFile a
          rb = getRangeWithoutFile b

          ra0 = rStart ra
          rb0 = rStart rb

          ra1 = rEnd ra
          rb1 = rEnd rb
      in
      if ra1 <= rb0 then
        (a:) <$> go as' bs
      else if rb1 <= ra0 then
        (b:) <$> go as bs'
      else do
        tell [(a,b)]
        if ra0 < rb0 || (ra0 == rb0 && ra1 <= rb1) then
          (a:) <$> go as' bs
        else
          (b:) <$> go as bs'
