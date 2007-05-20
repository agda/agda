-- | Types used for precise syntax highlighting.

module Interaction.Highlighting.Precise
  ( Aspect(..)
  , NameKind(..)
  , MetaInfo(..)
  , File
  , Range(..)
  , rangeInvariant
  , overlapping
  , empty
  , singleton
  , several
  , smallestPos
  , compress
  , tests
  ) where

import Utils.TestHelpers hiding (tests)
import Utils.Function
import Utils.String
import Utils.List hiding (tests)
import Data.List
import Data.Monoid
import Control.Monad
import Test.QuickCheck
import Data.Map (Map)
import qualified Data.Map as Map

------------------------------------------------------------------------
-- Files

-- | Various more or less syntactic aspects of the code.

data Aspect
  = Error
  | Comment
  | Keyword
  | String
  | Number
  | Name NameKind Bool -- ^ Is the name an operator part?
    deriving (Eq, Show)

data NameKind
  = Bound        -- ^ Bound variable.
  | Constructor
  | Datatype
  | Field        -- ^ Record field.
  | Function
  | Postulate
  | Primitive    -- ^ Primitive.
  | Record       -- ^ Record type.
    deriving (Eq, Show, Enum, Bounded)

-- | Meta information which can be associated with a
-- character/character range.

data MetaInfo = MetaInfo
  { aspect :: Maybe Aspect
  , dotted :: Bool
    -- ^ Is the range part of a dotted pattern?
  , note   :: Maybe String
    -- ^ This note, if present, can be displayed as a tool-tip or
    -- something like that. It should contain useful information about
    -- the range (like the module containing a certain identifier, or
    -- the fixity of an operator).
  }
  deriving (Eq, Show)

-- | 'MetaInfo' template.

empty :: MetaInfo
empty = MetaInfo { aspect = Nothing
                 , dotted = False
                 , note   = Nothing
                 }

-- | A 'File' is a mapping from file positions to meta information.
--
-- The first position in the file has number 1.

newtype File = File { mapping :: Map Integer MetaInfo }
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Ranges

-- | Character ranges. The first character in the file has position 1.
-- Note that the 'to' position is considered to be outside of the
-- range.
--
-- Invariant: @'from' '<=' 'to'@.

data Range = Range { from, to :: Integer }
             deriving (Eq, Show)

-- | The 'Range' invariant.

rangeInvariant :: Range -> Bool
rangeInvariant r = from r <= to r

-- | 'True' iff the ranges overlap.
--
-- The ranges are assumed to be well-formed.

overlapping :: Range -> Range -> Bool
overlapping r1 r2 = not $
  to r1 <= from r2 || to r2 <= from r1

-- | Converts a range to a list of positions.

toList :: Range -> [Integer]
toList r = [from r .. to r - 1]

-- | Returns the smallest position, if any, in the 'File'.

smallestPos :: File -> Maybe Integer
smallestPos = fmap (fst . snd) . Map.minView . mapping

------------------------------------------------------------------------
-- Creation

-- | @'singleton' r m@ is a file whose positions are those in @r@, and
-- in which every position is associated with @m@.

singleton :: Range -> MetaInfo -> File
singleton r m = File {
 mapping = Map.fromAscList [ (p, m) | p <- [from r .. to r - 1] ] }

prop_singleton r m =
  compress (singleton r m) ==
    if null (toList r) then [] else [(r, m)]

-- | Like 'singleton', but with several ranges instead of only one.

several :: [Range] -> MetaInfo -> File
several rs m = mconcat $ map (\r -> singleton r m) rs

------------------------------------------------------------------------
-- Merging

-- | Merges meta information.

mergeMetaInfo :: MetaInfo -> MetaInfo -> MetaInfo
mergeMetaInfo m1 m2 = MetaInfo
  { aspect = (mplus `on` aspect) m1 m2
  , dotted = ((||)  `on` dotted) m1 m2
  , note = case (note m1, note m2) of
      (Just n1, Just n2) -> Just $
         if n1 == n2 then n1
                     else addFinalNewLine n1 ++ "----\n" ++ n2
      (Just n1, Nothing) -> Just n1
      (Nothing, Just n2) -> Just n2
      (Nothing, Nothing) -> Nothing
  }

-- | Merges files.

merge :: File -> File -> File
merge f1 f2 =
  File { mapping = (Map.unionWith mergeMetaInfo `on` mapping) f1 f2 }

instance Monoid File where
  mempty  = File { mapping = Map.empty }
  mappend = merge

------------------------------------------------------------------------
-- Compression

-- | Compresses a file by merging consecutive positions with equal
-- meta information into longer ranges.

compress :: File -> [(Range, MetaInfo)]
compress f = map join $ groupBy' p (Map.toAscList $ mapping f)
  where
  p (pos1, m1) (pos2, m2) = pos2 == pos1 + 1 && m1 == m2
  join pms = ( Range { from = head ps, to = last ps + 1 }
             , head ms
             )
    where (ps, ms) = unzip pms 

prop_compress f =
  toFile c == f
  &&
  and (map (rangeInvariant . fst) c)
  &&
  and [ not (overlapping r1 r2) | (r1, r2) <- allPairs (map fst c) ]
  where
    c = compress f

    toFile = mconcat . map (uncurry singleton)

    allPairs []       = []
    allPairs (x : xs) = map ((,) x) xs ++ allPairs xs

------------------------------------------------------------------------
-- Generators

instance Arbitrary Aspect where
  arbitrary =
    frequency [ (2, elements [Comment, Keyword, String, Number])
              , (1, liftM2 Name arbitrary arbitrary)
              ]

  coarbitrary Error       = variant 0
  coarbitrary Comment     = variant 1
  coarbitrary Keyword     = variant 2
  coarbitrary String      = variant 3
  coarbitrary Number      = variant 4
  coarbitrary (Name nk b) = variant 5 . coarbitrary nk . coarbitrary b

instance Arbitrary NameKind where
  arbitrary   = elements [minBound .. maxBound]
  coarbitrary = coarbitrary . fromEnum

instance Arbitrary MetaInfo where
  arbitrary = do
    aspect <- maybeGen arbitrary
    dotted <- arbitrary
    note   <- maybeGen (list $ elements "abcdefABCDEF\"'@()åäö\n")
    return (MetaInfo { aspect = aspect, dotted = dotted, note = note })
  coarbitrary (MetaInfo aspect dotted note) =
    maybe' coarbitrary aspect .
    coarbitrary dotted .
    maybe' (coarbitrary . map fromEnum) note
    where
    maybe' f Nothing  = variant 0
    maybe' f (Just x) = variant 1 . f x

instance Arbitrary File where
  arbitrary = fmap (File . Map.fromList) $ list arbitrary
  coarbitrary (File rs) = coarbitrary (Map.toAscList rs)

instance Arbitrary Range where
  arbitrary = do
    [from, to] <- fmap sort $ listOfLength 2 positive
    return $ Range { from = from, to = to }
  coarbitrary (Range f t) = coarbitrary f . coarbitrary t

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO ()
tests = do
  quickCheck rangeInvariant
  quickCheck prop_singleton
  quickCheck prop_compress
