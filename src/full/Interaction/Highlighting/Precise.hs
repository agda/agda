-- | Types used for precise syntax highlighting.

module Interaction.Highlighting.Precise
  ( Aspect(..)
  , MetaInfo(..)
  , File(..)
  , Range(..)
  , rangeInvariant
  , overlapping
  , compress
  , tests
  ) where

import Utils.TestHelpers hiding (tests)
import Utils.Function
import Utils.String
import Utils.List hiding (tests)
import Data.List
import Data.Monoid
import Test.QuickCheck
import Data.Map (Map)
import qualified Data.Map as Map

------------------------------------------------------------------------
-- Types

-- | Various syntactic aspects of the code.

data Aspect
  = Bound        -- ^ Bound variable.
  | Comment
  | Constructor
  | Dotted       -- ^ Dotted pattern.
  | Function
  | Keyword
  | Number
  | Operator
  | Postulate
  | String
  | Type
    deriving (Eq, Ord, Read, Show, Enum, Bounded)

-- | Meta information which can be associated with a
-- character/character range.

data MetaInfo = MetaInfo
  { aspects  :: [Aspect]
    -- ^ Note that some aspects may not combine well in the user
    -- interface, depending on how the various aspects are
    -- represented. It is probably a good idea to document here which
    -- the possible combinations are, so that the UI designer can take
    -- them into account.
  , note     :: Maybe String
    -- ^ This note, if present, can be displayed as a tool-tip or
    -- something like that. It should contain useful information about
    -- the range (like the module containing a certain identifier, or
    -- the fixity of an operator).
  }
  deriving Show

instance Eq MetaInfo where
  (==) = ((==) `on` note) .&&. ((==) `on` (sort . aspects))
    where f1 .&&. f2 = \x y -> f1 x y && f2 x y

-- | A 'File' is a mapping from file positions to meta information.
--
-- The first position in the file has number 1.

newtype File = File { mapping :: Map Integer MetaInfo }
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Merging

-- | Merges meta information.

mergeMetaInfo :: MetaInfo -> MetaInfo -> MetaInfo
mergeMetaInfo m1 m2 = MetaInfo
  { aspects = nub $ ((++) `on` aspects) m1 m2
  , note = case (note m1, note m2) of
      (Just n1, Just n2) -> Just $
         if n1 == n2 then n1
                     else addFinalNewLine n1 ++ "----\n" ++ n2
      (Just n1, Nothing) -> Just n1
      (Nothing, Just n2) -> Just n2
      (Nothing, Nothing) -> Nothing
  }

instance Monoid MetaInfo where
  mempty  = MetaInfo { aspects = [], note = Nothing }
  mappend = mergeMetaInfo

-- | Merges files.

merge :: File -> File -> File
merge f1 f2 =
  File { mapping = (Map.unionWith mappend `on` mapping) f1 f2 }

instance Monoid File where
  mempty  = File { mapping = Map.empty }
  mappend = merge

------------------------------------------------------------------------
-- Compression

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

    toFile = File . Map.fromAscList . concatMap split
    split (r, m) = [ (p, m) | p <- [from r .. to r - 1] ]

    allPairs []       = []
    allPairs (x : xs) = map ((,) x) xs ++ allPairs xs

------------------------------------------------------------------------
-- Generators

instance Arbitrary Aspect where
  arbitrary   = elements [minBound .. maxBound]
  coarbitrary = coarbitrary . fromEnum

instance Arbitrary MetaInfo where
  arbitrary = do
    aspects <- list arbitrary
    note <- frequency [ (1, return Nothing)
                      , (9, fmap Just $ list $
                              elements "abcdefABCDEF\"'@()åäö\n")
                      ]
    return (MetaInfo { aspects = aspects, note = note })
  coarbitrary (MetaInfo asps Nothing)  = variant 0 . coarbitrary asps
  coarbitrary (MetaInfo asps (Just n)) =
    variant 1 . coarbitrary asps . coarbitrary (map fromEnum n)

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
  quickCheck prop_compress
