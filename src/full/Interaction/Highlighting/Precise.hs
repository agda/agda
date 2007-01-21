-- | Types used for precise syntax highlighting.

module Interaction.Highlighting.Precise
  ( Aspect(..)
  , Range(..)
  , rangeInvariant
  , overlapping
  , File(..)
  , fileInvariant
  , tests
  ) where

import Utils.TestHelpers hiding (tests)
import Data.List
import Test.QuickCheck

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
    deriving (Eq, Read, Show, Enum, Bounded)

-- | Character ranges. The first character in the file has position 1.
-- Note that the 'to' position is considered to be outside of the
-- range.
--
-- A range is associated with zero or more aspects. Note that some
-- aspects may not combine well in the user interface, depending on
-- how the various aspects are represented. It is probably a good idea
-- to document here which the possible combinations are, so that the
-- UI designer can take them into account.
--
-- Invariant: @'from' '<=' 'to'@.

data Range = Range { from, to :: Integer
                   , aspects  :: [Aspect]
                   , note     :: Maybe String
                     -- ^ This note, if present, can be displayed as a
                     -- tool-tip or something like that. It should
                     -- contain useful information about the range
                     -- (like the module containing a certain
                     -- identifier, or the fixity of an operator).
                   }
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

-- | A 'File' is a collection of 'Range's.
--
-- Invariant: All ranges should be non-overlapping.

newtype File = File { ranges :: [Range] }
               deriving (Eq, Show)

-- | The 'File' invariant.

fileInvariant :: File -> Bool
fileInvariant f = not $ or [ overlapping r1 r2
                           | (r1, r2) <- allPairs $ ranges f
                           ]
  where
  allPairs []       = []
  allPairs (x : xs) = map ((,) x) xs ++ allPairs xs

------------------------------------------------------------------------
-- Generators

instance Arbitrary Aspect where
  arbitrary   = elements [minBound .. maxBound]
  coarbitrary = coarbitrary . fromEnum

instance Arbitrary Range where
  arbitrary = do
    [from, to] <- fmap sort $ listOfLength 2 positive
    aspects    <- list arbitrary
    note       <- frequency
                    [ (1, return Nothing)
                    , (9, fmap Just $
                            list $ elements "abcdefABCDEF\"'@()åäö")
                    ]
    return $ Range { from    = from
                   , to      = to
                   , aspects = aspects
                   , note    = note }

  coarbitrary (Range f t a Nothing) = variant 0 .
    coarbitrary f . coarbitrary t . coarbitrary a
  coarbitrary (Range f t a (Just n)) = variant 1 .
    coarbitrary f . coarbitrary t . coarbitrary a .
    coarbitrary (map fromEnum n)

instance Arbitrary File where
  arbitrary = fmap (File . dropOverlapping) $ list arbitrary
    where
    dropOverlapping []       = []
    dropOverlapping (r : rs) | any (overlapping r) rs = rest
                             | otherwise              = r : rest
      where rest = dropOverlapping rs
  coarbitrary (File rs) = coarbitrary rs

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO ()
tests = do
  quickCheck rangeInvariant
  quickCheck fileInvariant
