-- | Data structures for collecting CPU usage.

module Agda.TypeChecking.Monad.Base.Benchmark where

import qualified Agda.Utils.Maybe.Strict as Strict
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
  | BinaryEncode
    -- ^ Subphase for 'Serialize'.
  | Compress
    -- ^ Subphase for 'Serialize'.
  | Operators
    -- ^ Subphase for 'Parsing'.
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Account we can bill computation time to.
--   A word of 'Phase's.
type Account = [Phase]

-- | Benchmark structure is a trie, mapping accounts (phases and subphases)
--   to CPU time spent on their performance.
data Benchmark = Benchmark
  { currentAccount :: !(Strict.Maybe Account)
  , timings        :: !(Trie Phase CPUTime)
  }

-- | Semantic editor combinator.
modifyCurrentAccount ::
  (Strict.Maybe Account -> Strict.Maybe Account) ->
  Benchmark -> Benchmark
modifyCurrentAccount f b = b { currentAccount = f (currentAccount b) }

-- | Semantic editor combinator.
modifyTimings ::
  (Trie Phase CPUTime -> Trie Phase CPUTime) ->
  Benchmark -> Benchmark
modifyTimings f b = b { timings = f (timings b) }

-- | Initial benchmark structure (empty).
empty :: Benchmark
empty =
  Benchmark { currentAccount = Strict.Nothing, timings = Trie.empty }

-- | Add to specified CPU time account.
addCPUTime :: Account -> CPUTime -> Benchmark -> Benchmark
addCPUTime acc t = modifyTimings (Trie.insertWith (+) acc t)

-- -- | Lens modifier for specific entry in benchmark structure.
-- mapCPUTime :: [Phase] → (CPUTime -> CPUTime) -> Benchmark -> Benchmark
-- mapCPUtime k f = inserWith
