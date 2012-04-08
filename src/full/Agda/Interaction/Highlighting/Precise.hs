{-# LANGUAGE DeriveDataTypeable, CPP #-}

-- | Types used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Precise
  ( Aspect(..)
  , NameKind(..)
  , OtherAspect(..)
  , MetaInfo(..)
  , File
  , HighlightingInfo
  , InteractionOutputCallback
  , defaultInteractionOutputCallback
  , singleton
  , several
  , smallestPos
  , toMap
  , CompressedFile
  , compress
  , decompress
  , Agda.Interaction.Highlighting.Precise.tests
  ) where

import Agda.Utils.TestHelpers
import Agda.Utils.String
import Agda.Utils.List hiding (tests)
import Data.List
import Data.Function
import Data.Monoid
import Control.Monad
import Agda.Utils.QuickCheck
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Generics (Typeable, Data)

import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Common as C
import qualified Agda.Syntax.Concrete as SC

import Agda.Interaction.Highlighting.Range
import {-# SOURCE #-} Agda.Interaction.Response (Response)

#include "../../undefined.h"
import Agda.Utils.Impossible

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
    deriving (Eq, Show, Typeable, Data)

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
    deriving (Eq, Show, Typeable, Data)

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
  | TypeChecked
    -- ^ Code which has been type-checked but not yet properly
    -- highlighted.
    deriving (Eq, Show, Enum, Bounded, Typeable, Data)

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
  deriving (Eq, Show, Typeable, Data)

-- | A 'File' is a mapping from file positions to meta information.
--
-- The first position in the file has number 1.

newtype File = File { mapping :: Map Integer MetaInfo }
  deriving (Eq, Show, Typeable, Data)

-- | Returns the smallest position, if any, in the 'File'.

smallestPos :: File -> Maybe Integer
smallestPos = fmap (fst . fst) . Map.minViewWithKey . mapping

-- | Syntax highlighting information for a given source file.

type HighlightingInfo = CompressedFile

-- | Callback fuction to call when there is a response
--   to give to the interactive frontend.
--
--   Note that the response is given in pieces and incrementally,
--   so the user can have timely response even during long computations.
--
--   Typical 'InteractionOutputCallback' functions:
--
--    * Convert the response into a 'String' representation and
--      print it on standard output
--      (suitable for inter-process communication).
--
--    * Put the response into a mutable variable stored in the
--      closure of the 'InteractionOutputCallback' function.
--      (suitable for intra-process communication).

type InteractionOutputCallback = Response -> IO ()

-- | The default 'InteractionOutputCallback' function
--   is set to __IMPOSSIBLE__ because in this way
--   it is easier to recognize that some response is lost
--   due to an uninitialized 'InteractionOutputCallback' function.

defaultInteractionOutputCallback :: InteractionOutputCallback
defaultInteractionOutputCallback = __IMPOSSIBLE__

------------------------------------------------------------------------
-- Creation

-- | @'singleton' r m@ is a file whose positions are those in @r@, and
-- in which every position is associated with @m@.

singleton :: Range -> MetaInfo -> File
singleton r m = File {
 mapping = Map.fromAscList [ (p, m) | p <- toList r ] }

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
-- Inspection

-- | Convert the 'File' to a map from file positions (counting from 1)
-- to meta information.

toMap :: File -> Map Integer MetaInfo
toMap = mapping

------------------------------------------------------------------------
-- Compression

-- | A compressed 'File', in which consecutive positions with the same
-- 'MetaInfo' are stored together.

type CompressedFile = [(Range, MetaInfo)]

-- | Compresses a file by merging consecutive positions with equal
-- meta information into longer ranges.

compress :: File -> CompressedFile
compress f = map join $ groupBy' p (Map.toAscList $ mapping f)
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
  map (\(r, m) -> [ (p, m) | p <- toList r ])

prop_compress f =
  decompress c == f
  &&
  and (map (rangeInvariant . fst) c)
  &&
  and [ not (overlapping r1 r2) | (r1, r2) <- allPairs (map fst c) ]
  where
    c = compress f

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

instance CoArbitrary MetaInfo where
  coarbitrary (MetaInfo aspect otherAspects note defSite) =
    coarbitrary aspect .
    coarbitrary otherAspects .
    coarbitrary note .
    coarbitrary defSite

instance Arbitrary File where
  arbitrary = fmap (File . Map.fromList) $ listOf arbitrary

instance CoArbitrary File where
  coarbitrary (File rs) = coarbitrary (Map.toAscList rs)

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Precise"
  [ quickCheck' prop_singleton
  , quickCheck' prop_compress
  ]
