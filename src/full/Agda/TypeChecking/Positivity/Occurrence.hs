{-# OPTIONS_GHC -Wunused-imports #-}

-- | Occurrences.

module Agda.TypeChecking.Positivity.Occurrence where

import Prelude hiding (null)
import Control.DeepSeq

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Position
import Agda.Utils.List1 (List1)
import Agda.Utils.Null
import Agda.Utils.SemiRing

-- Occurrences
----------------------------------------------------------------------------------------------------

-- | List of polarities stemming from POLARITY pragma.
type PragmaPolarities = List1 (Ranged Occurrence)

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
  | Unused    -- ^ No occurrence.
  deriving (Show, Eq, Ord, Enum, Bounded)

instance P.Pretty Occurrence where
  pretty = P.text . \case
    Unused    -> "_"
    Mixed     -> "*"
    JustNeg   -> "-"
    JustPos   -> "+"
    StrictPos -> "++"
    GuardPos  -> "g+"

instance NFData Occurrence where rnf x = seq x ()

instance KillRange Occurrence where killRange = id

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

modalPolarityToOccurrence :: ModalPolarity -> Occurrence
modalPolarityToOccurrence = \case
  UnusedPolarity   -> Unused
  StrictlyPositive -> StrictPos
  Positive         -> JustPos
  Negative         -> JustNeg
  MixedPolarity    -> Mixed

-- Paths to occurrences
----------------------------------------------------------------------------------------------------

data OccursPath
  = Root
  | LeftOfArrow !OccursPath
  | DefArg !OccursPath !QName !Nat      -- ^ in the nth argument of a defined constant
  | MutDefArg !OccursPath !Int !Nat     -- ^ in the nth argument of a def in the current mutual block.
                                        --   (def given by Int index in the block)
  | UnderInf !OccursPath                -- ^ in the principal argument of built-in ∞
  | VarArg !OccursPath !Nat !Occurrence -- ^ as an argument to a bound variable with given polarity.
                                        --   The polarity is only used for warning printing.
  | MetaArg !OccursPath                 -- ^ as an argument of a metavariable
  | ConArgType !OccursPath !QName       -- ^ in the type of a constructor
  | IndArgType !OccursPath !QName       -- ^ in a datatype index of a constructor
  | ConEndpoint !OccursPath !QName      -- ^ in an endpoint of a higher constructor
  | InClause !OccursPath !Nat           -- ^ in the nth clause of a defined function
  | Matched !OccursPath                 -- ^ matched against in a clause of a defined function
  | InIndex !OccursPath                 -- ^ is an index of an inductive family
  | InDefOf !OccursPath !QName          -- ^ in the definition of a constant
  deriving Eq

instance NFData OccursPath where
  rnf x = seq x ()

instance Show OccursPath where
  show p = go p [] where
    go p acc = case p of
      Root            -> acc
      LeftOfArrow p   -> go p $ " InLeftOfArrow" ++ acc
      DefArg p q i    -> go p $ " InDefArg "      ++ P.prettyShow q ++ " " ++ P.prettyShow i ++ acc
      MutDefArg p q i -> go p $ " InMutDefArg "   ++ P.prettyShow q ++ " " ++ P.prettyShow i ++ acc
      UnderInf p      -> go p $ " InUnderInf" ++ acc
      VarArg p i o    -> go p $ " InVarArg "      ++ P.prettyShow i ++ " " ++ P.prettyShow o ++ acc
      MetaArg p       -> go p $ " InMetaArg" ++ acc
      ConArgType p q  -> go p $ " InConArgType "  ++ P.prettyShow q ++ acc
      IndArgType p q  -> go p $ " InIndArgType "  ++ P.prettyShow q ++ acc
      ConEndpoint p q -> go p $ " InConEndpoint " ++ P.prettyShow q ++ acc
      InClause p i    -> go p $ " InClause "    ++ P.prettyShow i ++ acc
      Matched p       -> go p $ " Matched" ++ acc
      InIndex p       -> go p $ " InIndex" ++ acc
      InDefOf p q     -> go p $ " InDefOf " ++ P.prettyShow q ++ acc

instance P.Pretty OccursPath where
  pretty = P.text . show

data OccursWhere = OccursWhere !Range !OccursPath
  deriving (Eq, Show)

instance P.Pretty OccursWhere where
  pretty (OccursWhere x y) = "OccursWhere" P.<+> P.pretty x P.<+> P.pretty y

--------------------------------------------------------------------------------

data Edge a = Edge !Occurrence !a
  deriving (Eq, Ord, Show, Functor)

mergeEdges :: Edge a -> Edge a -> Edge a
mergeEdges _                    e@(Edge Mixed _)     = e -- dominant
mergeEdges e@(Edge Mixed _)     _                    = e
mergeEdges (Edge Unused _)      e                    = e -- neutral
mergeEdges e                    (Edge Unused _)      = e
mergeEdges (Edge JustNeg _)     e@(Edge JustNeg _)   = e
mergeEdges _                    e@(Edge JustNeg a)   = Edge Mixed a
mergeEdges e@(Edge JustNeg a)   _                    = Edge Mixed a
mergeEdges _                    e@(Edge JustPos _)   = e -- dominates strict pos.
mergeEdges e@(Edge JustPos _)   _                    = e
mergeEdges _                    e@(Edge StrictPos _) = e -- dominates 'GuardPos'
mergeEdges e@(Edge StrictPos _) _                    = e
mergeEdges (Edge GuardPos _)    e@(Edge GuardPos _)  = e

instance Monoid a => SemiRing (Edge a) where
  ozero = Edge ozero mempty
  oone  = Edge oone  mempty
  oplus = mergeEdges
  otimes (Edge o1 w1) (Edge o2 w2) = Edge (otimes o1 o2) (w1 <> w2)
