{-# OPTIONS_GHC -Wunused-imports #-}

-- | Occurrences.

module Agda.TypeChecking.Positivity.Occurrence
  ( PragmaPolarities
  , Occurrence(..)
  , OccursWhere(..)
  , modalPolarityToOccurrence
  ) where

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

data OccursWhere
  = Root
  | LeftOfArrow !OccursWhere
  | DefArg !OccursWhere !QName !Nat    -- ^ in the nth argument of a defined constant
  | MutDefArg !OccursWhere !QName !Nat -- ^ in the nth argument of a def in the current mutual block
  | UnderInf !OccursWhere              -- ^ in the principal argument of built-in ∞
  | VarArg !OccursWhere !Nat           -- ^ as an argument to a bound variable.
  | MetaArg !OccursWhere               -- ^ as an argument of a metavariable
  | ConArgType !OccursWhere !QName     -- ^ in the type of a constructor
  | IndArgType !OccursWhere !QName     -- ^ in a datatype index of a constructor
  | ConEndpoint !OccursWhere !QName    -- ^ in an endpoint of a higher constructor
  | InClause !OccursWhere !Nat         -- ^ in the nth clause of a defined function
  | Matched !OccursWhere               -- ^ matched against in a clause of a defined function
  | IsIndex !OccursWhere               -- ^ is an index of an inductive family
  | InDefOf !OccursWhere !QName        -- ^ in the definition of a constant
  deriving Eq

instance NFData OccursWhere where
  rnf x = seq x ()

instance Show OccursWhere where
  show p = go p [] where
    go p acc = case p of
      Root            -> acc
      LeftOfArrow p   -> go p $ " InLeftOfArrow" ++ acc
      DefArg p q i    -> go p $ " InDefArg "      ++ P.prettyShow q ++ " " ++ P.prettyShow i ++ acc
      MutDefArg p q i -> go p $ " InMutDefArg "   ++ P.prettyShow q ++ " " ++ P.prettyShow i ++ acc
      UnderInf p      -> go p $ " InUnderInf" ++ acc
      VarArg p i      -> go p $ " InVarArg "      ++ P.prettyShow i ++ acc
      MetaArg p       -> go p $ " InMetaArg" ++ acc
      ConArgType p q  -> go p $ " InConArgType "  ++ P.prettyShow q ++ acc
      IndArgType p q  -> go p $ " InIndArgType "  ++ P.prettyShow q ++ acc
      ConEndpoint p q -> go p $ " InConEndpoint " ++ P.prettyShow q ++ acc
      InClause p i    -> go p $ " InClause "    ++ P.prettyShow i ++ acc
      Matched p       -> go p $ " Matched" ++ acc
      IsIndex p       -> go p $ " IsIndex" ++ acc
      InDefOf p q     -> go p $ " InDefOf " ++ P.prettyShow q ++ acc

instance P.Pretty OccursWhere where
  pretty = P.text . show
