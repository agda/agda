{-# OPTIONS_GHC -fwarn-missing-signatures #-}

-- | Data structures for collecting CPU usage.

module Agda.TypeChecking.Monad.Base.Benchmark where

import Agda.Utils.Trie as Trie
import Agda.Utils.Time (CPUTime)

-- | Phases to allocate CPU time to.
data Phase
  = Parsing
    -- ^ Happy parsing and operator parsing.
  | Import
    -- ^ Import chasing.
  | Deserialization
    -- ^ Reading interface files.
  | Scoping
    -- ^ Scope checking and translation to abstract syntax.
  | Typing
    -- ^ Type checking and translation to internal syntax.
  | Termination
    -- ^ Termination checking.
  | Positivity
    -- ^ Positivity checking and polarity computation.
  | Injectivity
    -- ^ Injectivity checking.
  | ProjectionLikeness
    -- ^ Checking for projection likeness.
  | Coverage
    -- ^ Coverage checking and compilation to case trees.
  | Highlighting
    -- ^ Generating highlighting info.
  | Serialization
    -- ^ Writing interface files.
  | Graph
    -- ^ Subphase for 'Termination'.
  | RecCheck
    -- ^ Subphase for 'Termination'.
  | Reduce
    -- ^ Subphase for 'Termination'.
  | Level
    -- ^ Subphase for 'Termination'.
  | Compare
    -- ^ Subphase for 'Termination'.
  | With
    -- ^ Subphase for 'Termination'.
  | ModuleName
    -- ^ Subphase for 'Import'.
  | Sort
    -- ^ Subphase for 'Serialize'.
  | Operators
    -- ^ Subphase for 'Parsing'.
  | BuildParser
    -- ^ Subphase for 'Operators'.
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Account we can bill computation time to.
type Account = [Phase]

-- | Benchmark structure is a trie, mapping phases (and subphases)
--   to CPU time spent on their performance.
type Benchmark = Trie Phase CPUTime

-- | Initial benchmark structure (empty).
empty :: Benchmark
empty = Trie.empty

-- | Add to specified CPU time account.
addCPUTime :: Account -> CPUTime -> Benchmark -> Benchmark
addCPUTime = Trie.insertWith (+)

-- -- | Lens modifier for specific entry in benchmark structure.
-- mapCPUTime :: [Phase] → (CPUTime -> CPUTime) -> Benchmark -> Benchmark
-- mapCPUtime k f = inserWith
