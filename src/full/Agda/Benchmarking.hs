{-# LANGUAGE CPP                       #-}
{-# LANGUAGE IncoherentInstances       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Agda-specific benchmarking structure.

module Agda.Benchmarking where

import qualified Control.Exception as E

import Data.IORef

import System.IO.Unsafe

import Agda.Syntax.Concrete.Name (TopLevelModuleName)
import Agda.Syntax.Concrete.Pretty
import Agda.Syntax.Abstract.Name
import Agda.Utils.Benchmark (MonadBench(..))
import qualified Agda.Utils.Benchmark as B
import Agda.Utils.Null
import Agda.Utils.Pretty

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
    -- ^ Deac code elimination.
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
  deriving (Eq, Ord, Show)

instance Pretty Phase where
  pretty (TopModule m)  = pretty m
  pretty (Definition q) = pretty q
  pretty a = text (show a)

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

instance MonadBench Phase IO where
  getBenchmark = readIORef benchmarks
  putBenchmark = writeIORef benchmarks
  finally = E.finally

-- | Benchmark an IO computation and bill it to the given account.
billToIO :: Account -> IO a -> IO a
billToIO = B.billTo

-- | Benchmark a pure computation and bill it to the given account.
billToPure :: Account -> a -> a
billToPure acc a = unsafePerformIO $ billToIO acc $ return a
