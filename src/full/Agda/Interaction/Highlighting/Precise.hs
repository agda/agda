-- | Types used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Precise
  ( -- * Highlighting information
    Aspect(..)
  , NameKind(..)
  , OtherAspect(..)
  , Aspects(..)
  , DefinitionSite(..)
  , TokenBased(..)
  , RangePair(..)
  , rangePairInvariant
  , PositionMap(..)
  , DelayedMerge(..)
  , delayedMergeInvariant
  , HighlightingInfo
  , highlightingInfoInvariant
  , HighlightingInfoBuilder
  , highlightingInfoBuilderInvariant
    -- ** Operations
  , parserBased
  , kindOfNameToNameKind
  , IsBasicRangeMap(..)
  , RangeMap.several
  , Convert(..)
  , RangeMap.insideAndOutside
  , RangeMap.restrictTo
  ) where

import Prelude hiding (null)

import Control.DeepSeq

import Data.Function (on)
import Data.Semigroup

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set

import GHC.Generics (Generic)

import qualified Agda.Syntax.Common   as Common
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Scope.Base                   ( KindOfName(..) )

import Agda.Interaction.Highlighting.Range

import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.RangeMap (RangeMap, IsBasicRangeMap(..))
import qualified Agda.Utils.RangeMap as RangeMap

import Agda.Syntax.Common.Aspect
import Agda.Utils.String

import Agda.Utils.Impossible

-- | A limited kind of syntax highlighting information: a pair
-- consisting of 'Ranges' and 'Aspects'.
--
-- Note the invariant which 'RangePair's should satisfy
-- ('rangePairInvariant').

newtype RangePair = RangePair
  { rangePair :: (Ranges, Aspects)
  }
  deriving (Show, NFData)

-- | Invariant for 'RangePair'.

rangePairInvariant :: RangePair -> Bool
rangePairInvariant (RangePair (rs, _)) =
  rangesInvariant rs

-- | Syntax highlighting information, represented by maps from
-- positions to 'Aspects'.
--
-- The first position in the file has number 1.

newtype PositionMap = PositionMap
  { positionMap :: IntMap Aspects
  }
  deriving (Show, NFData)

-- | Highlighting info with delayed merging.
--
-- Merging large sets of highlighting info repeatedly might be costly.
-- The idea of this type is to accumulate small pieces of highlighting
-- information, and then to merge them all at the end.
--
-- Note the invariant which values of this type should satisfy
-- ('delayedMergeInvariant').

newtype DelayedMerge hl = DelayedMerge (Endo [hl])
  deriving (Semigroup, Monoid)

instance Show hl => Show (DelayedMerge hl) where
  showsPrec _ (DelayedMerge f) =
    showString "DelayedMerge (Endo (" .
    shows (appEndo f []) .
    showString " ++))"

-- | Invariant for @'DelayedMerge' hl@, parametrised by the invariant
-- for @hl@.
--
-- Additionally the endofunction should be extensionally equal to @(fs
-- '++')@ for some list @fs@.

delayedMergeInvariant :: (hl -> Bool) -> DelayedMerge hl -> Bool
delayedMergeInvariant inv (DelayedMerge f) =
  all inv (appEndo f [])

-- | Highlighting information.
--
-- Note the invariant which values of this type should satisfy
-- ('highlightingInfoInvariant').
--
-- This is a type synonym in order to make it easy to change to
-- another representation.

type HighlightingInfo = RangeMap Aspects

-- | The invariant for 'HighlightingInfo'.

highlightingInfoInvariant :: HighlightingInfo -> Bool
highlightingInfoInvariant = RangeMap.rangeMapInvariant

-- | A type that is intended to be used when constructing highlighting
-- information.
--
-- Note the invariant which values of this type should satisfy
-- ('highlightingInfoBuilderInvariant').
--
-- This is a type synonym in order to make it easy to change to
-- another representation.
--
-- The type should be an instance of @'IsBasicRangeMap' 'Aspects'@,
-- 'Semigroup' and 'Monoid', and there should be an instance of
-- @'Convert' 'HighlightingInfoBuilder' 'HighlightingInfo'@.

type HighlightingInfoBuilder = DelayedMerge RangePair

-- | The invariant for 'HighlightingInfoBuilder'.
--
-- Additionally the endofunction should be extensionally equal to @(fs
-- '++')@ for some list @fs@.

highlightingInfoBuilderInvariant :: HighlightingInfoBuilder -> Bool
highlightingInfoBuilderInvariant =
  delayedMergeInvariant rangePairInvariant

------------------------------------------------------------------------
-- Creation and conversion

-- | A variant of 'mempty' with 'tokenBased' set to
-- 'NotOnlyTokenBased'.

parserBased :: Aspects
parserBased = mempty { tokenBased = NotOnlyTokenBased }

-- | Conversion from classification of the scope checker.

kindOfNameToNameKind :: KindOfName -> NameKind
kindOfNameToNameKind = \case
  -- Inductive is Constructor default, overwritten by CoInductive
  ConName                  -> Constructor Common.Inductive
  CoConName                -> Constructor Common.CoInductive
  FldName                  -> Field
  PatternSynName           -> Constructor Common.Inductive
  GeneralizeName           -> Generalizable
  DisallowedGeneralizeName -> Generalizable
  MacroName                -> Macro
  QuotableName             -> Function
  DataName                 -> Datatype
  RecName                  -> Record
  FunName                  -> Function
  AxiomName                -> Postulate
  PrimName                 -> Primitive
  OtherDefName             -> Function

instance IsBasicRangeMap Aspects RangePair where
  singleton rs m = RangePair (rs, m)

  toList (RangePair (Ranges rs, m)) =
    [ (r, m) | r <- rs, not (null r) ]

  toMap f = toMap (convert (DelayedMerge (Endo (f :))) :: PositionMap)

instance IsBasicRangeMap Aspects PositionMap where
  singleton rs m = PositionMap
    { positionMap =
      IntMap.fromDistinctAscList [ (p, m) | p <- rangesToPositions rs ]
    }

  toList = map join . List1.groupBy' p . IntMap.toAscList . positionMap
    where
    p (pos1, m1) (pos2, m2) = pos2 == pos1 + 1 && m1 == m2
    join pms = ( Range { from = List1.head ps, to = List1.last ps + 1 }
               , List1.head ms
               )
      where (ps, ms) = List1.unzip pms

  toMap = positionMap

instance Semigroup a =>
         IsBasicRangeMap a (DelayedMerge (RangeMap a)) where
  singleton r m = DelayedMerge (Endo (singleton r m :))

  toMap  f = toMap  (convert f :: RangeMap a)
  toList f = toList (convert f :: RangeMap a)

instance IsBasicRangeMap Aspects (DelayedMerge RangePair) where
  singleton r m = DelayedMerge (Endo (singleton r m :))

  toMap  f = toMap  (convert f :: PositionMap)
  toList f = toList (convert f :: RangeMap Aspects)

instance IsBasicRangeMap Aspects (DelayedMerge PositionMap) where
  singleton r m = DelayedMerge (Endo (singleton r m :))

  toMap  f = toMap  (convert f :: PositionMap)
  toList f = toList (convert f :: PositionMap)

-- | Conversion between different types.

class Convert a b where
  convert :: a -> b

instance Monoid hl => Convert (DelayedMerge hl) hl where
  convert (DelayedMerge f) = mconcat (appEndo f [])

instance Convert (RangeMap Aspects) (RangeMap Aspects) where
  convert = id

instance Convert PositionMap (RangeMap Aspects) where
  convert =
    RangeMap.fromNonOverlappingNonEmptyAscendingList .
    toList

instance Convert (DelayedMerge PositionMap) (RangeMap Aspects) where
  convert f = convert (convert f :: PositionMap)

instance Convert (DelayedMerge RangePair) PositionMap where
  convert (DelayedMerge f) =
    PositionMap $
    IntMap.fromListWith (flip (<>))
      [ (p, m)
      | RangePair (r, m) <- appEndo f []
      , p                <- rangesToPositions r
      ]

instance Convert (DelayedMerge RangePair) (RangeMap Aspects) where
  convert (DelayedMerge f) =
    mconcat
      [ singleton r m
      | RangePair (r, m) <- appEndo f []
      ]

------------------------------------------------------------------------
-- Merging

instance Semigroup TokenBased where
  b1@NotOnlyTokenBased <> b2 = b1
  TokenBased           <> b2 = b2

instance Monoid TokenBased where
  mempty  = TokenBased
  mappend = (<>)


instance Semigroup DefinitionSite where
  d1 <> d2 | d1 == d2  = d1
           | otherwise = d1 -- TODO: __IMPOSSIBLE__

-- | Merges meta information.

mergeAspects :: Aspects -> Aspects -> Aspects
mergeAspects m1 m2 = Aspects
  { aspect       = (unionMaybeWith (<>) `on` aspect) m1 m2
  , otherAspects = (Set.union `on` otherAspects) m1 m2
  , note         = case (note m1, note m2) of
      (n1, "") -> n1
      ("", n2) -> n2
      (n1, n2)
        | n1 == n2  -> n1
        | otherwise -> addFinalNewLine n1 ++ "----\n" ++ n2
  , definitionSite = (unionMaybeWith (<>) `on` definitionSite) m1 m2
  , tokenBased     = tokenBased m1 <> tokenBased m2
  }

instance Semigroup Aspects where
  (<>) = mergeAspects

instance Monoid Aspects where
  mempty = Aspects
    { aspect         = Nothing
    , otherAspects   = Set.empty
    , note           = []
    , definitionSite = Nothing
    , tokenBased     = mempty
    }
  mappend = (<>)

instance Semigroup PositionMap where
  f1 <> f2 = PositionMap
    { positionMap = (IntMap.unionWith mappend `on` positionMap) f1 f2 }

instance Monoid PositionMap where
  mempty  = PositionMap { positionMap = IntMap.empty }
  mappend = (<>)

------------------------------------------------------------------------
-- NFData instances

instance NFData Aspect
instance NFData OtherAspect
instance NFData DefinitionSite

instance NFData Aspects where
  rnf (Aspects a b c d _) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d
