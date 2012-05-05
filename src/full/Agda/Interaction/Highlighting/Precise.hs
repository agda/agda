{-# LANGUAGE DeriveDataTypeable #-}

-- | Types used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Precise
  ( -- * Files
    Aspect(..)
  , NameKind(..)
  , OtherAspect(..)
  , MetaInfo(..)
  , File
  , HighlightingInfo
    -- ** Creation
  , singleton
  , several
    -- ** Inspection
  , smallestPos
  , toMap
    -- * Compressed files
  , CompressedFile(..)
  , compressedFileInvariant
  , compress
  , decompress
    -- ** Creation
  , singletonC
  , severalC
  , splitAtC
    -- ** Inspection
  , smallestPosC
    -- * Tests
  , Agda.Interaction.Highlighting.Precise.tests
  ) where

import Agda.Utils.TestHelpers
import Agda.Utils.String
import Agda.Utils.List hiding (tests)
import Data.List
import Data.Function
import Data.Monoid
import Control.Applicative ((<$>), (<*>))
import Control.Arrow ((&&&))
import Control.Monad
import Agda.Utils.QuickCheck hiding (ranges)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Typeable (Typeable)

import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Common as C
import qualified Agda.Syntax.Concrete as SC
import qualified Agda.Syntax.Position as P

import Agda.Interaction.Highlighting.Range

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
    deriving (Eq, Show, Typeable)

data NameKind
  = Bound                   -- ^ Bound variable.
  | Constructor C.Induction -- ^ Inductive or coinductive constructor.
  | Datatype
  | Field                   -- ^ Record field.
  | Function
  | Module                  -- ^ Module name.
  | Postulate
  | Primitive               -- ^ Primitive.
  | Record                  -- ^ Record type.
    deriving (Eq, Show, Typeable)

-- | Other aspects. (These can overlap with each other and with
-- 'Aspect's.)

data OtherAspect
  = Error
  | DottedPattern
  | UnsolvedMeta
  | UnsolvedConstraint
    -- ^ Unsolved constraint not connected to meta-variable. This
    -- could for instance be an emptyness constraint.
  | TerminationProblem
  | IncompletePattern
    -- ^ When this constructor is used it is probably a good idea to
    -- include a 'note' explaining why the pattern is incomplete.
  | TypeChecks
    -- ^ Code which is being type-checked.
    deriving (Eq, Show, Enum, Bounded, Typeable)

-- | Meta information which can be associated with a
-- character\/character range.

data MetaInfo = MetaInfo
  { aspect       :: Maybe Aspect
  , otherAspects :: [OtherAspect]
  , note         :: Maybe String
    -- ^ This note, if present, can be displayed as a tool-tip or
    -- something like that. It should contain useful information about
    -- the range (like the module containing a certain identifier, or
    -- the fixity of an operator).
  , definitionSite :: Maybe (SC.TopLevelModuleName, Integer)
    -- ^ The definition site of the annotated thing, if applicable and
    --   known. File positions are counted from 1.
  }
  deriving (Eq, Show, Typeable)

-- | A 'File' is a mapping from file positions to meta information.
--
-- The first position in the file has number 1.

newtype File = File { mapping :: Map Integer MetaInfo }
  deriving (Eq, Show, Typeable)

-- | Syntax highlighting information.

type HighlightingInfo = CompressedFile

------------------------------------------------------------------------
-- Creation

-- | @'singleton' rs m@ is a file whose positions are those in @rs@,
-- and in which every position is associated with @m@.

singleton :: Ranges -> MetaInfo -> File
singleton rs m = File {
 mapping = Map.fromAscList [ (p, m) | p <- rangesToPositions rs ] }

-- | Like 'singleton', but with several 'Ranges' instead of only one.

several :: [Ranges] -> MetaInfo -> File
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
-- Inspection

-- | Returns the smallest position, if any, in the 'File'.

smallestPos :: File -> Maybe Integer
smallestPos = fmap (fst . fst) . Map.minViewWithKey . mapping

-- | Convert the 'File' to a map from file positions (counting from 1)
-- to meta information.

toMap :: File -> Map Integer MetaInfo
toMap = mapping

------------------------------------------------------------------------
-- Compressed files

-- | A compressed 'File', in which consecutive positions with the same
-- 'MetaInfo' are stored together.

newtype CompressedFile =
  CompressedFile { ranges :: [(Range, MetaInfo)] }
  deriving (Eq, Show, Typeable)

-- | Invariant for compressed files.
--
-- Note that these files are not required to be /maximally/
-- compressed, because ranges are allowed to be empty, and the
-- 'MetaInfo's in adjacent ranges are allowed to be equal.

compressedFileInvariant :: CompressedFile -> Bool
compressedFileInvariant (CompressedFile []) = True
compressedFileInvariant (CompressedFile f)  =
  all rangeInvariant rs &&
  all (not . empty) rs &&
  and (zipWith (<=) (map to $ init rs) (map from $ tail rs))
  where rs = map fst f

-- | Compresses a file by merging consecutive positions with equal
-- meta information into longer ranges.

compress :: File -> CompressedFile
compress f =
  CompressedFile $ map join $ groupBy' p (Map.toAscList $ mapping f)
  where
  p (pos1, m1) (pos2, m2) = pos2 == pos1 + 1 && m1 == m2
  join pms = ( Range { from = head ps, to = last ps + 1 }
             , head ms
             )
    where (ps, ms) = unzip pms

-- | Decompresses a compressed file.

decompress :: CompressedFile -> File
decompress =
  File .
  Map.fromList .
  concat .
  map (\(r, m) -> [ (p, m) | p <- rangeToPositions r ]) .
  ranges

prop_compress f =
  compressedFileInvariant c
  &&
  decompress c == f
  where c = compress f

------------------------------------------------------------------------
-- Operations that work directly with compressed files

-- | @'singletonC' rs m@ is a file whose positions are those in @rs@,
-- and in which every position is associated with @m@.

singletonC :: Ranges -> MetaInfo -> CompressedFile
singletonC (Ranges rs) m =
  CompressedFile [(r, m) | r <- rs, not (empty r)]

prop_singleton rs m = singleton rs m == decompress (singletonC rs m)

-- | Like 'singletonR', but with a list of 'Ranges' instead of a
-- single one.

severalC :: [Ranges] -> MetaInfo -> CompressedFile
severalC rss m = mconcat $ map (\rs -> singletonC rs m) rss

prop_several rss m = several rss m == decompress (severalC rss m)

-- | Merges compressed files.

mergeC :: CompressedFile -> CompressedFile -> CompressedFile
mergeC (CompressedFile f1) (CompressedFile f2) =
  CompressedFile (mrg f1 f2)
  where
  mrg []             f2             = f2
  mrg f1             []             = f1
  mrg (p1@(i1,_):f1) (p2@(i2,_):f2)
    | to i1 <= from i2 = p1 : mrg f1      (p2:f2)
    | to i2 <= from i1 = p2 : mrg (p1:f1) f2
    | to i1 <= to i2   = ps1 ++ mrg f1 (ps2 ++ f2)
    | otherwise        = ps1 ++ mrg (ps2 ++ f1) f2
      where (ps1, ps2) = fuse p1 p2

  -- Precondition: The ranges are overlapping.
  fuse (i1, m1) (i2, m2) =
    ( fix [ (Range { from = a, to = b }, ma)
          , (Range { from = b, to = c }, mergeMetaInfo m1 m2)
          ]
    , fix [ (Range { from = c, to = d }, md)
          ]
    )
    where
    [(a, ma), (b, _), (c, _), (d, md)] =
      sortBy (compare `on` fst)
             [(from i1, m1), (to i1, m1), (from i2, m2), (to i2, m2)]
    fix = filter (not . empty . fst)

prop_merge f1 f2 =
  merge f1 f2 == decompress (mergeC (compress f1) (compress f2))

instance Monoid CompressedFile where
  mempty  = CompressedFile []
  mappend = mergeC

-- | @splitAtC p f@ splits the compressed file @f@ into @(f1, f2)@,
-- where all the positions in @f1@ are @< p@, and all the positions
-- in @f2@ are @>= p@.

splitAtC :: Integer -> CompressedFile ->
            (CompressedFile, CompressedFile)
splitAtC p f = (CompressedFile f1, CompressedFile f2)
  where
  (f1, f2) = split $ ranges f

  split [] = ([], [])
  split (rx@(r,x) : f)
    | p <= from r = ([], rx:f)
    | to r <= p   = (rx:f1, f2)
    | otherwise   = ([ (toP, x) ], (fromP, x) : f)
    where (f1, f2) = split f
          toP      = Range { from = from r, to = p    }
          fromP    = Range { from = p,      to = to r }

prop_splitAtC p f =
  all (<  p) (positions f1) &&
  all (>= p) (positions f2) &&
  decompress (mergeC f1 f2) == decompress f
  where
  (f1, f2) = splitAtC p f

  positions = Map.keys . toMap . decompress

-- | Returns the smallest position, if any, in the 'CompressedFile'.

smallestPosC :: CompressedFile -> Maybe Integer
smallestPosC (CompressedFile [])           = Nothing
smallestPosC (CompressedFile ((r, _) : _)) = Just (from r)

prop_smallestPos f = smallestPos (decompress f) == smallestPosC f

------------------------------------------------------------------------
-- Generators

instance Arbitrary Aspect where
  arbitrary =
    frequency [ (3, elements [ Comment, Keyword, String, Number
                             , Symbol, PrimitiveType ])
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

instance Arbitrary NameKind where
  arbitrary = oneof $ [liftM Constructor arbitrary] ++
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

instance Arbitrary OtherAspect where
  arbitrary = elements [minBound .. maxBound]

instance CoArbitrary OtherAspect where
  coarbitrary = coarbitrary . fromEnum

instance Arbitrary MetaInfo where
  arbitrary = do
    aspect  <- arbitrary
    other   <- arbitrary
    note    <- maybeGen string
    defSite <- arbitrary
    return (MetaInfo { aspect = aspect, otherAspects = other
                     , note = note, definitionSite = defSite })
    where string = listOfElements "abcdefABCDEF/\\.\"'@()åäö\n"

  shrink (MetaInfo a o n d) =
    [ MetaInfo a o n d | a <- shrink a ] ++
    [ MetaInfo a o n d | o <- shrink o ] ++
    [ MetaInfo a o n d | n <- shrink n ] ++
    [ MetaInfo a o n d | d <- shrink d ]

instance CoArbitrary MetaInfo where
  coarbitrary (MetaInfo aspect otherAspects note defSite) =
    coarbitrary aspect .
    coarbitrary otherAspects .
    coarbitrary note .
    coarbitrary defSite

instance Arbitrary File where
  arbitrary = fmap (File . Map.fromList) $ listOf arbitrary
  shrink    = map (File . Map.fromList) . shrink . Map.toList . toMap

instance CoArbitrary File where
  coarbitrary (File rs) = coarbitrary (Map.toAscList rs)

instance Arbitrary CompressedFile where
  arbitrary = do
    rs <- (\ns1 ns2 -> toRanges $ sort $
                         ns1 ++ concatMap (\n -> [n, succ n]) ns2) <$>
            arbitrary <*> arbitrary
    CompressedFile <$> mapM (\r -> (,) r <$> arbitrary) rs
    where
    toRanges (f : t : rs)
      | f == t    = toRanges (t : rs)
      | otherwise = Range { from = f, to = t } :
                    toRanges (case rs of
                                f : rs | t == f -> rs
                                _               -> rs)
    toRanges _ = []

  shrink (CompressedFile f) = CompressedFile <$> shrink f

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Precise"
  [ quickCheck' compressedFileInvariant
  , quickCheck' (all compressedFileInvariant . shrink)
  , quickCheck' (\r m -> compressedFileInvariant $ singletonC r m)
  , quickCheck' (\rs m -> compressedFileInvariant $ severalC rs m)
  , quickCheck' (\f1 f2 -> compressedFileInvariant $ mergeC f1 f2)
  , quickCheck' (\i f -> all compressedFileInvariant $
                         (\(f1, f2) -> [f1, f2]) $
                         splitAtC i f)
  , quickCheck' prop_compress
  , quickCheck' prop_singleton
  , quickCheck' prop_several
  , quickCheck' prop_merge
  , quickCheck' prop_splitAtC
  , quickCheck' prop_smallestPos
  ]
