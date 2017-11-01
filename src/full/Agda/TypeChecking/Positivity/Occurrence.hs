{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}


-- | Occurrences.

module Agda.TypeChecking.Positivity.Occurrence
  ( Occurrence(..)
  , OccursWhere(..)
  , Where(..)
  , boundToEverySome
  , productOfEdgesInBoundedWalk
  ) where

import Control.DeepSeq
import Control.Monad

import Data.Data (Data)
import Data.Either
import Data.Foldable (toList)
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Position

import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Graph)
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.List
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.SemiRing

#include "undefined.h"
import Agda.Utils.Impossible

-- Specification of occurrences -------------------------------------------

-- Operations and instances in Agda.TypeChecking.Positivity.

-- | Description of an occurrence.
data OccursWhere
  = Unknown
    -- ^ an unknown position (treated as negative)
  | Known Range (Seq Where)
    -- ^ The elements of the sequence, from left to right, explain how
    -- to get to the occurrence.
  deriving (Show, Eq, Ord, Data)

-- | One part of the description of an occurrence.
data Where
  = LeftOfArrow
  | DefArg QName Nat -- ^ in the nth argument of a define constant
  | UnderInf         -- ^ in the principal argument of built-in ∞
  | VarArg           -- ^ as an argument to a bound variable
  | MetaArg          -- ^ as an argument of a metavariable
  | ConArgType QName -- ^ in the type of a constructor
  | IndArgType QName -- ^ in a datatype index of a constructor
  | InClause Nat     -- ^ in the nth clause of a defined function
  | Matched          -- ^ matched against in a clause of a defined function
  | InDefOf QName    -- ^ in the definition of a constant
  deriving (Show, Eq, Ord, Data)

-- | Subterm occurrences for positivity checking.
--   The constructors are listed in increasing information they provide:
--   @Mixed <= JustPos <= StrictPos <= GuardPos <= Unused@
--   @Mixed <= JustNeg <= Unused@.
data Occurrence
  = Mixed     -- ^ Arbitrary occurrence (positive and negative).
  | JustNeg   -- ^ Negative occurrence.
  | JustPos   -- ^ Positive occurrence, but not strictly positive.
  | StrictPos -- ^ Strictly positive occurrence.
  | GuardPos  -- ^ Guarded strictly positive occurrence (i.e., under ∞).  For checking recursive records.
  | Unused    --  ^ No occurrence.
  deriving (Data, Show, Eq, Ord, Enum, Bounded)

-- * Pretty instances

instance Pretty Occurrence where
  pretty = text . \case
    Unused    -> "_"
    Mixed     -> "*"
    JustNeg   -> "-"
    JustPos   -> "+"
    StrictPos -> "++"
    GuardPos  -> "g+"

instance Pretty Where where
  pretty = \case
    LeftOfArrow  -> text "LeftOfArrow"
    DefArg q i   -> text "DefArg"     <+> pretty q <+> pretty i
    UnderInf     -> text "UnderInf"
    VarArg       -> text "VarArg"
    MetaArg      -> text "MetaArg"
    ConArgType q -> text "ConArgType" <+> pretty q
    IndArgType q -> text "IndArgType" <+> pretty q
    InClause i   -> text "InClause"   <+> pretty i
    Matched      -> text "Matched"
    InDefOf q    -> text "InDefOf"    <+> pretty q

instance Pretty OccursWhere where
  pretty = \case
    Unknown     -> text "Unknown"
    Known _r ws -> text "Known _" <+> pretty (toList ws)

-- * Instances for 'Occurrence'

instance NFData Occurrence where rnf x = seq x ()

instance KillRange Occurrence where
  killRange = id

-- | 'Occurrence' is a complete lattice with least element 'Mixed'
--   and greatest element 'Unused'.
--
--   It forms a commutative semiring where 'oplus' is meet (glb)
--   and 'otimes' is composition. Both operations are idempotent.
--
--   For 'oplus', 'Unused' is neutral (zero) and 'Mixed' is dominant.
--   For 'otimes', 'StrictPos' is neutral (one) and 'Unused' is dominant.

instance SemiRing Occurrence where
  ozero = Unused
  oone  = StrictPos

  oplus Mixed _           = Mixed     -- dominant
  oplus _ Mixed           = Mixed
  oplus Unused o          = o         -- neutral
  oplus o Unused          = o
  oplus JustNeg  JustNeg  = JustNeg
  oplus JustNeg  o        = Mixed     -- negative and any form of positve
  oplus o        JustNeg  = Mixed
  oplus GuardPos o        = o         -- second-rank neutral
  oplus o GuardPos        = o
  oplus StrictPos o       = o         -- third-rank neutral
  oplus o StrictPos       = o
  oplus JustPos JustPos   = JustPos

  otimes Unused _            = Unused     -- dominant
  otimes _ Unused            = Unused
  otimes Mixed _             = Mixed      -- second-rank dominance
  otimes _ Mixed             = Mixed
  otimes JustNeg JustNeg     = JustPos
  otimes JustNeg _           = JustNeg    -- third-rank dominance
  otimes _ JustNeg           = JustNeg
  otimes JustPos _           = JustPos    -- fourth-rank dominance
  otimes _ JustPos           = JustPos
  otimes GuardPos _          = GuardPos   -- _ `elem` [StrictPos, GuardPos]
  otimes _ GuardPos          = GuardPos
  otimes StrictPos StrictPos = StrictPos  -- neutral

instance StarSemiRing Occurrence where
  ostar Mixed     = Mixed
  ostar JustNeg   = Mixed
  ostar JustPos   = JustPos
  ostar StrictPos = StrictPos
  ostar GuardPos  = StrictPos
  ostar Unused    = StrictPos

instance Null Occurrence where
  empty = Unused

-- | The map contains bindings of the form @bound |-> ess@, satisfying
-- the following property: for every non-empty list @w@,
-- @'foldr1' 'otimes' w '<=' bound@ iff
-- @'or' [ 'all' every w '&&' 'any' some w | (every, some) <- ess ]@.

boundToEverySome ::
  Map Occurrence [(Occurrence -> Bool, Occurrence -> Bool)]
boundToEverySome = Map.fromList
  [ ( JustPos
    , [((/= Unused), (`elem` [Mixed, JustNeg, JustPos]))]
    )
  , ( StrictPos
    , [ ((/= Unused), (`elem` [Mixed, JustNeg, JustPos]))
      , ((not . (`elem` [Unused, GuardPos])), const True)
      ]
    )
  , ( GuardPos
    , [((/= Unused), const True)]
    )
  ]

-- | @productOfEdgesInBoundedWalk occ g u v bound@ returns @'Just' e@
-- iff there is a walk @c@ (a list of edges) in @g@, from @u@ to @v@,
-- for which the product @'foldr1' 'otimes' ('map' occ c) '<=' bound@.
-- In this case the returned value @e@ is the product @'foldr1'
-- 'otimes' c@ for one such walk.
--
-- Preconditions: @u@ and @v@ must belong to @g@, and @bound@ must
-- belong to the domain of @boundToEverySome@.

-- There is a property for this function in
-- Agda.Utils.Graph.AdjacencyMap.Unidirectional.Tests.

productOfEdgesInBoundedWalk ::
  (SemiRing e, Ord n) =>
  (e -> Occurrence) -> Graph n n e -> n -> n -> Occurrence -> Maybe e
productOfEdgesInBoundedWalk occ g u v bound =
  case Map.lookup bound boundToEverySome of
    Nothing  -> __IMPOSSIBLE__
    Just ess ->
      case msum [ Graph.walkSatisfying (every . occ) (some . occ) g u v
                | (every, some) <- ess
                ] of
        Just es@(_ : _) -> Just (foldr1 otimes (map Graph.label es))
        Just []         -> __IMPOSSIBLE__
        Nothing         -> Nothing
