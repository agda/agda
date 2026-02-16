
{-# LANGUAGE Strict #-}
-- {-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Positivity.NewOccurrence where

import Prelude hiding ( null, (!!) )

import Control.Applicative hiding (empty)
import Control.DeepSeq
import Control.Monad.Reader ( MonadReader(..), asks, ReaderT, runReaderT )

import Data.Either
import qualified Data.Foldable as Fold
import Data.Function (on)
import Data.Graph (SCC(..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as DS
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Strict.These

import Debug.Trace

import Agda.Interaction.Options.Base (optOccurrence)
import Agda.Syntax.Common
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position (HasRange(..), noRange)
import Agda.TypeChecking.Datatypes ( isDataOrRecordType )
import Agda.TypeChecking.Functions
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Benchmark (MonadBench, Phase)
import Agda.TypeChecking.Monad.Benchmark qualified as Bench
import Agda.TypeChecking.Patterns.Match ( properlyMatching )
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings

import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.Function (applyUnless)
import Agda.Utils.Functor
import Agda.Utils.List
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Common.Pretty (Pretty, prettyShow)
import Agda.Utils.SemiRing
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.StrictReader

import Agda.Utils.Impossible

import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Graph)
import Agda.Utils.Graph.AdjacencyMap.Unidirectional qualified as Graph

--------------------------------------------------------------------------------

data Path
  = Root
  | DefArg Path QName Nat         -- ^ in the nth argument of a defined constant
  | UnderInf Path                 -- ^ in the principal argument of built-in ∞
  | VarArg Path Occurrence Nat    -- ^ as an argument to a bound variable.
                                  --   The polarity, if given, is the polarity of
                                  --   the argument the occurence is in
  | MetaArg Path                  -- ^ as an argument of a metavariable
  | ConArgType Path QName         -- ^ in the type of a constructor
  | IndArgType Path QName         -- ^ in a datatype index of a constructor
  | ConEndpoint Path QName        -- ^ in an endpoint of a higher constructor
  | InClause Path Nat             -- ^ in the nth clause of a defined function
  | Matched Path                  -- ^ matched against in a clause of a defined function
  | IsIndex Path                  -- ^ is an index of an inductive family
  | InDefOf Path QName            -- ^ in the definition of a constant
  deriving (Eq, Ord, Show)

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

instance Pretty Occurrence where
  pretty = text . \case
    Unused    -> "_"
    Mixed     -> "*"
    JustNeg   -> "-"
    JustPos   -> "+"
    StrictPos -> "++"
    GuardPos  -> "g+"

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

instance Null Occurrence where
  empty = Unused

data Node = DefNode !QName | ArgNode !QName !Nat
  deriving (Eq, Ord)

data OccEnv = OccEnv {
    vars   :: [[Occurrence]] -- ^ Occurrence info for definitions args.
  , inf    :: Maybe QName    -- ^ Name for ∞ builtin.
  , locals :: Int            -- ^ Number of local binders (on the top of the definition args).
  }

-- class ComputeOccurrences a where
--   occurrences











--------------------------------------------------------------------------------
