{-# OPTIONS_GHC -Wunused-imports #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Agda-specific benchmarking structure.

module Agda.Benchmarking where

import Control.DeepSeq
import qualified Control.Exception as E

import Data.IORef

import GHC.Generics (Generic)

import System.IO.Unsafe

import Agda.Syntax.Concrete.Pretty () --instance only
import Agda.Syntax.Abstract.Name
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import Agda.Utils.Benchmark (MonadBench(..))
import qualified Agda.Utils.Benchmark as B
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty

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
  | DeadCode
    -- ^ Dead code elimination.
  | DeadCodeInstantiateFull
    -- ^ Unfolding all metas before serialization.
  | DeadCodeReachable
    -- ^ Dead code reachable definitions subphase.
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
  | TypeBasedTermination
    -- ^ Type-based termination checking.
  | SizeTypeEncoding
    -- ^ Subphase for 'TypeBasedTermination': converting internal terms to size expressions.
  | PatternRigids
    -- ^ Subphase for 'TypeBasedTermination': computing rigid variables from patterns.
  | SizeTypeChecking
    -- ^ Subphase for 'TypeBasedTermination': bidirectional checking of clause bodies.
  | Preservation
    -- ^ Subphase for 'TypeBasedTermination': size-preservation checking.
  | SizeGraphSolving
    -- ^ Subphase for 'TypeBasedTermination': solving the size constraints.
  | Cluster
    -- ^ Subphase for 'TypeBasedTermination': solving the size constraints.
  | Matrix
    -- ^ Subphase for 'TypeBasedTermination': processing size-change matrices.
  | ModuleName
    -- ^ Subphase for 'Import'.
  | Compaction
    -- ^ Subphase for 'Deserialization': compacting interfaces.
  | BuildInterface
    -- ^ Subphase for 'Serialization'.
  | Sort
    -- ^ Subphase for 'Serialization'.
  | BinaryEncode
    -- ^ Subphase for 'Serialization'.
  | Compress
    -- ^ Subphase for 'Serialization'.
  | OperatorsExpr
    -- ^ Subphase for 'Parsing'.
  | OperatorsPattern
    -- ^ Subphase for 'Parsing'.
  | Free
    -- ^ Subphase for 'Typing': free variable computation.
  | OccursCheck
    -- ^ Subphase for 'Typing': occurs check for solving metas.
  | CheckLHS
    -- ^ Subphase for 'Typing': checking the LHS
  | CheckRHS
    -- ^ Subphase for 'Typing': checking the RHS
  | TypeSig
    -- ^ Subphase for 'Typing': checking a type signature
  | Generalize
    -- ^ Subphase for 'Typing': generalizing over `variable`s
  | InstanceSearch
    -- ^ Subphase for 'Typing': solving instance goals
  | UnifyIndices
    -- ^ Subphase for 'CheckLHS': unification of the indices
  | InverseScopeLookup
    -- ^ Pretty printing names.
  | TopModule TopLevelModuleName
  | Definition QName
  deriving (Eq, Ord, Show, Generic)

instance Pretty Phase where
  pretty (TopModule m)  = pretty m
  pretty (Definition q) = pretty q
  pretty a = text (show a)

instance NFData Phase

type Benchmark = B.Benchmark Phase
type Account   = B.Account Phase

isModuleAccount :: Account -> Bool
isModuleAccount []                = True
isModuleAccount (TopModule{} : _) = True
isModuleAccount _                 = False

isDefAccount :: Account -> Bool
isDefAccount []                 = True
isDefAccount (Definition{} : _) = True
isDefAccount _                  = False

isInternalAccount :: Account -> Bool
isInternalAccount (TopModule{}  : _) = False
isInternalAccount (Definition{} : _) = False
isInternalAccount _                  = True

-- * Benchmarking in the IO monad.

-- | Global variable to store benchmark statistics.
{-# NOINLINE benchmarks #-}
benchmarks :: IORef Benchmark
benchmarks = unsafePerformIO $ newIORef empty

instance MonadBench IO where
  type BenchPhase IO = Phase
  getBenchmark = readIORef benchmarks
  putBenchmark = writeIORef benchmarks
  finally = E.finally

-- | Benchmark an IO computation and bill it to the given account.
billToIO :: Account -> IO a -> IO a
billToIO = B.billTo

-- | Benchmark a pure computation and bill it to the given account.
billToPure :: Account -> a -> a
billToPure acc a = unsafePerformIO $ billToIO acc $ return a
{-# NOINLINE billToPure #-}
