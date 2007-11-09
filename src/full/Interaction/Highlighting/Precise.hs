-- | Types used for precise syntax highlighting.

module Interaction.Highlighting.Precise
  ( Aspect(..)
  , NameKind(..)
  , OtherAspect(..)
  , MetaInfo(..)
  , File
  , singleton
  , several
  , smallestPos
  , compress
  , Interaction.Highlighting.Precise.tests
  ) where

import Utils.TestHelpers
import Utils.Function
import Utils.String
import Utils.List hiding (tests)
import Data.List
import Data.Monoid
import Control.Monad
import Test.QuickCheck
import Data.Map (Map)
import qualified Data.Map as Map

import Interaction.Highlighting.Range

------------------------------------------------------------------------
-- Files

-- | Various more or less syntactic aspects of the code. (These cannot
-- overlap.)

data Aspect
  = Comment
  | Keyword
  | String
  | Number
  | Symbol                     -- ^ Symbols like forall, =, ->, etc.
  | PrimitiveType              -- ^ Things like Set and Prop.
  | Name (Maybe NameKind) Bool -- ^ Is the name an operator part?
    deriving (Eq, Show)

data NameKind
  = Bound        -- ^ Bound variable.
  | Constructor
  | Datatype
  | Field        -- ^ Record field.
  | Function
  | Module       -- ^ Module name.
  | Postulate
  | Primitive    -- ^ Primitive.
  | Record       -- ^ Record type.
    deriving (Eq, Show, Enum, Bounded)

-- | Other aspects. (These can overlap with each other and with
-- 'Aspect's.)

data OtherAspect
  = Error
  | DottedPattern
  | UnsolvedMeta
  | TerminationProblem
  | IncompletePattern
    -- ^ When this constructor is used it is probably a good idea to
    -- include a 'note' explaining why the pattern is incomplete.
    deriving (Eq, Show, Enum, Bounded)

-- | Meta information which can be associated with a
-- character/character range.

data MetaInfo = MetaInfo
  { aspect       :: Maybe Aspect
  , otherAspects :: [OtherAspect]  
  , note         :: Maybe String
    -- ^ This note, if present, can be displayed as a tool-tip or
    -- something like that. It should contain useful information about
    -- the range (like the module containing a certain identifier, or
    -- the fixity of an operator).
  , definitionSite :: Maybe (FilePath, Integer)
    -- ^ This can be the definition site of the given name.
  }
  deriving (Eq, Show)

-- | A 'File' is a mapping from file positions to meta information.
--
-- The first position in the file has number 1.

newtype File = File { mapping :: Map Integer MetaInfo }
  deriving (Eq, Show)

-- | Returns the smallest position, if any, in the 'File'.

smallestPos :: File -> Maybe Integer
smallestPos = fmap (fst . fst) . Map.minViewWithKey . mapping

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
  { aspect       = (mplus `on` aspect) m1 m2
  , otherAspects = nub $ ((++) `on` otherAspects) m1 m2
  , note         = case (note m1, note m2) of
      (Just n1, Just n2) -> Just $
         if n1 == n2 then n1
                     else addFinalNewLine n1 ++ "----\n" ++ n2
      (Just n1, Nothing) -> Just n1
      (Nothing, Just n2) -> Just n2
      (Nothing, Nothing) -> Nothing
  , definitionSite = (mplus `on` definitionSite) m1 m2
  }

instance Monoid MetaInfo where
  mempty = MetaInfo { aspect         = Nothing
                    , otherAspects   = []
                    , note           = Nothing
                    , definitionSite = Nothing
                    }
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
    frequency [ (3, elements [ Comment, Keyword, String, Number
                             , Symbol, PrimitiveType ])
              , (1, liftM2 Name (maybeGen arbitrary) arbitrary)
              ]

instance CoArbitrary Aspect where
  coarbitrary Comment       = variant 0
  coarbitrary Keyword       = variant 1
  coarbitrary String        = variant 2
  coarbitrary Number        = variant 3
  coarbitrary Symbol        = variant 4
  coarbitrary PrimitiveType = variant 5
  coarbitrary (Name nk b)   =
    variant 6 . maybeCoGen coarbitrary nk . coarbitrary b

instance Arbitrary NameKind where
  arbitrary   = elements [minBound .. maxBound]

instance CoArbitrary NameKind where
  coarbitrary = coarbitrary . fromEnum

instance Arbitrary OtherAspect where
  arbitrary   = elements [minBound .. maxBound]

instance CoArbitrary OtherAspect where
  coarbitrary = coarbitrary . fromEnum

instance Arbitrary MetaInfo where
  arbitrary = do
    aspect  <- maybeGen arbitrary
    other   <- arbitrary
    note    <- maybeGen (listOfElements "abcdefABCDEF/\\.\"'@()åäö\n")
    defSite <- maybeGen (liftM2 (,)
                                (listOfElements "abcdefABCDEF/\\.\"'@()åäö\n")
                                arbitrary)
    return (MetaInfo { aspect = aspect, otherAspects = other, note = note
                     , definitionSite = defSite })

instance CoArbitrary MetaInfo where
  coarbitrary (MetaInfo aspect otherAspects note defSite) =
    maybeCoGen coarbitrary aspect .
    coarbitrary otherAspects .
    maybeCoGen (coarbitrary . map fromEnum) note .
    maybeCoGen (\(f, p) -> coarbitrary p . coarbitrary (map fromEnum f))
               defSite

instance Arbitrary File where
  arbitrary = fmap (File . Map.fromList) $ listOf arbitrary

instance CoArbitrary File where
  coarbitrary (File rs) = coarbitrary (Map.toAscList rs)

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO ()
tests = do
  quickCheck prop_singleton
  quickCheck prop_compress
