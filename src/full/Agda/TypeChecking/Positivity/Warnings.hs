-- {-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Positivity.Warnings where

import Prelude hiding (null)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.DeepSeq

import Data.Foldable (toList, msum)
import Data.Sequence (Seq)
import qualified Data.Sequence as DS
import GHC.Generics

import Agda.Interaction.Options.Base (optOccurrence)
import Agda.Syntax.Common
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position (HasRange(..), noRange, Range)
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Common.Pretty (Pretty, prettyShow)
import Agda.TypeChecking.Positivity.Occurrence (Occurrence(..))

import Agda.Utils.SemiRing
import Agda.Utils.Null
import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Graph)
import Agda.Utils.Graph.AdjacencyMap.Unidirectional qualified as Graph
import Agda.Utils.Impossible

----------------------------------------------------------------------------------------------------

-- | Description of an occurrence.
data OccursWhere
  = OccursWhere Range (Seq Where) (Seq Where)
    -- ^ The elements of the sequences, read from left to right,
    -- explain how to get to the occurrence. The second sequence
    -- includes the main information, and if the first sequence is
    -- non-empty, then it includes information about the context of
    -- the second sequence.
  deriving (Show, Eq, Ord, Generic)

instance NFData OccursWhere

instance Null OccursWhere where
  empty = OccursWhere empty empty empty
  null (OccursWhere r wh1 wh2) = and [ null r, null wh1, null wh2 ]

-- | One part of the description of an occurrence.
data Where
  = LeftOfArrow
  | DefArg QName Nat       -- ^ in the nth argument of a define constant
  | UnderInf               -- ^ in the principal argument of built-in ∞
  | VarArg Occurrence Nat  -- ^ as an argument to a bound variable.
  | MetaArg                -- ^ as an argument of a metavariable
  | ConArgType QName       -- ^ in the type of a constructor
  | IndArgType QName       -- ^ in a datatype index of a constructor
  | ConEndpoint QName
                           -- ^ in an endpoint of a higher constructor
  | InClause Nat           -- ^ in the nth clause of a defined function
  | Matched                -- ^ matched against in a clause of a defined function
  | InIndex                -- ^ is an index of an inductive family
  | InDefOf QName          -- ^ in the definition of a constant
  deriving (Show, Eq, Ord, Generic)

instance NFData Where

instance Pretty Where where
  pretty = \case
    LeftOfArrow  -> "LeftOfArrow"
    DefArg q i   -> "DefArg"     <+> pretty q <+> pretty i
    UnderInf     -> "UnderInf"
    VarArg k i   -> "VarArg" <+> pretty k <+> pretty i
    MetaArg      -> "MetaArg"
    ConArgType q -> "ConArgType" <+> pretty q
    IndArgType q -> "IndArgType" <+> pretty q
    ConEndpoint q
                 -> "ConEndpoint" <+> pretty q
    InClause i   -> "InClause"   <+> pretty i
    Matched      -> "Matched"
    InIndex      -> "IsIndex"
    InDefOf q    -> "InDefOf"    <+> pretty q

instance Pretty OccursWhere where
  pretty = \case
    OccursWhere r ws1 ws2 ->
      "OccursWhere " <+> pretty r <+> pretty (toList ws1) <+> pretty (toList ws2)

-- | Edge labels for the positivity graph.
data Edge a = Edge !Occurrence a
  deriving (Eq, Ord, Show, Functor)

-- | Merges two edges between the same source and target.

mergeEdges :: Edge a -> Edge a -> Edge a
mergeEdges _                    e@(Edge Mixed _)     = e -- dominant
mergeEdges e@(Edge Mixed _)     _                    = e
mergeEdges (Edge Unused _)      e                    = e -- neutral
mergeEdges e                    (Edge Unused _)      = e
mergeEdges (Edge JustNeg _)     e@(Edge JustNeg _)   = e
mergeEdges _                    e@(Edge JustNeg w)   = Edge Mixed w
mergeEdges e@(Edge JustNeg w)   _                    = Edge Mixed w
mergeEdges _                    e@(Edge JustPos _)   = e -- dominates strict pos.
mergeEdges e@(Edge JustPos _)   _                    = e
mergeEdges _                    e@(Edge StrictPos _) = e -- dominates 'GuardPos'
mergeEdges e@(Edge StrictPos _) _                    = e
mergeEdges (Edge GuardPos _)    e@(Edge GuardPos _)  = e

-- | These operations form a semiring if we quotient by the relation
-- \"the 'Occurrence' components are equal\".

instance SemiRing (Edge (Seq OccursWhere)) where
  ozero = Edge ozero DS.empty
  oone  = Edge oone  DS.empty

  oplus = mergeEdges

  otimes (Edge o1 w1) (Edge o2 w2) = Edge (otimes o1 o2) (w1 DS.>< w2)

----------------------------------------------------------------------------------------------------

-- | The map contains bindings of the form @bound |-> ess@, satisfying
-- the following property: for every non-empty list @w@,
-- @'foldr1' 'otimes' w '<=' bound@ iff
-- @'or' [ 'all' every w '&&' 'any' some w | (every, some) <- ess ]@.

boundToEverySome ::
  Map Occurrence [(Occurrence -> Bool, Occurrence -> Bool)]
boundToEverySome = Map.fromListWith __IMPOSSIBLE__
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

-- | @productOfEdgesInBoundedWalk occ g u v bound@ returns a value
-- distinct from 'Nothing' iff there is a walk @c@ (a list of edges)
-- in @g@, from @u@ to @v@, for which the product @'foldr1' 'otimes'
-- ('map' occ c) '<=' bound@. In this case the returned value is
-- @'Just' ('foldr1' 'otimes' c)@ for one such walk @c@.
--
-- Preconditions: @u@ and @v@ must belong to @g@, and @bound@ must
-- belong to the domain of @boundToEverySome@.

-- There is a property for this function in
-- Internal.Utils.Graph.AdjacencyMap.Unidirectional.

productOfEdgesInBoundedWalk ::
  (SemiRing e, Ord n) =>
  (e -> Occurrence) -> Graph n e -> n -> n -> Occurrence -> Maybe e
productOfEdgesInBoundedWalk occ g u v bound =
  case Map.lookup bound boundToEverySome of
    Nothing  -> __IMPOSSIBLE__
    Just ess ->
      case msum [ Graph.walkSatisfying
                    (every . occ . Graph.label)
                    (some . occ . Graph.label)
                    g u v
                | (every, some) <- ess
                ] of
        Just es@(_ : _) -> Just (foldr1 otimes (map Graph.label es))
        Just []         -> __IMPOSSIBLE__
        Nothing         -> Nothing
