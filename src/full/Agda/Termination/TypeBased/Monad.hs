{-| This module contains the monad that is used to perform type-based termination checking.
-}

module Agda.Termination.TypeBased.Monad
  ( TBTM
  , runSizeChecker
  , SConstraint (..)
  , ConstrType (..)
  , MutualRecursiveCall (mrcNameFrom, mrcNameTo, mrcSizesFrom, mrcSizesTo, mrcPlace)
  -- * Graph manipulation
  , getCurrentConstraints
  , getTotalConstraints
  , storeConstraint
  -- * Size variables manipulation
  , getCurrentRigids
  , requestNewRigidVariable
  , withVariableCounter
  , getBottomVariables
  , storeBottomVariable
  , getLeafSizeVariables
  , setLeafSizeVariables
  , getInfiniteSizes
  , markInfiniteSize
  , getFallbackInstantiations
  , addFallbackInstantiation
  , getSizePolarity
  -- * Core variables manipulation
  , getCurrentCoreContext
  , appendCoreVariable
  , abstractCoreContext
  -- * Size preservation
  , replacePreservationCandidates
  , getRecursionMatrix
  , getPreservationCandidates
  , withAnotherPreservationCandidate
  , reportDirectRecursion
  -- * Definition manipulation
  , currentCheckedName
  , getRootArity
  , currentMutualNames
  , reportCall
  , freshenSignature
  , initNewClause
  , initSizePreservation
  , hasEncodingErrors
  , recordError
  ) where

import Control.Monad ( replicateM, forM )
import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class ( MonadIO )
import Control.Monad.Trans.State ( StateT, gets, modify, runStateT )
import qualified Data.IntMap as IntMap
import Data.IntMap ( IntMap )
import qualified Data.IntSet as IntSet
import Data.IntSet ( IntSet )
import qualified Data.Map as Map
import Data.Map ( Map)
import qualified Data.List as List
import Data.Maybe ( fromJust, mapMaybe )
import Data.Set ( Set )

import qualified Agda.Benchmarking as Benchmark
import qualified Agda.Syntax.Common.Pretty as P
import qualified Agda.Utils.Benchmark as B

import Agda.Termination.TypeBased.Common ( updateSizeVariables )
import Agda.Termination.TypeBased.Syntax ( SizeSignature(SizeSignature), SizeBound(..), FreeGeneric(fgIndex), SizeType, Size(..), sizeSigArity )
import Agda.TypeChecking.Monad.Base ( TCM, Definition(defSizedType), HasOptions, MonadTCM, MonadTCState, MonadTCEnv, Closure, ReadTCState )
import Agda.TypeChecking.Monad.Context ( MonadAddContext )
import Agda.TypeChecking.Monad.Debug ( MonadDebug, reportSDoc )
import Agda.TypeChecking.Monad.Signature ( HasConstInfo(getConstInfo) )
import Agda.TypeChecking.Monad.Statistics ( MonadStatistics )
import Agda.TypeChecking.Polarity ( composePol )
import Agda.TypeChecking.Polarity.Base ( Polarity (Invariant, Contravariant, Covariant) )
import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Internal ( QName, Term )

-- | This monad represents an environment for type checking internal terms against sie types.
newtype TBTM a = TBTM (StateT SizeCheckerState TCM a)
  deriving
  ( Functor
  , Applicative
  , Monad
  , MonadTCEnv
  , MonadTCState
  , HasOptions
  , MonadDebug
  , Fail.MonadFail
  , HasConstInfo
  , MonadAddContext
  , MonadIO
  , MonadTCM
  , ReadTCState
  , MonadStatistics
  )

instance B.MonadBench TBTM where
  type BenchPhase TBTM = Benchmark.Phase
  getBenchmark              = TBTM $ B.getBenchmark
  putBenchmark              = TBTM . B.putBenchmark
  modifyBenchmark           = TBTM . B.modifyBenchmark
  finally (TBTM m) (TBTM f) = TBTM $ (B.finally m f)

type SizeContextEntry = (Int, Either FreeGeneric SizeType)

data ConstrType = SLte | SLeq deriving (Eq, Ord)

instance P.Pretty ConstrType where
  pretty SLte = "<"
  pretty SLeq = "≤"

data SConstraint = SConstraint { scType :: ConstrType, scFrom :: Int, scTo :: Int }

-- | Represents a call between two mutually-recursive functions.
data MutualRecursiveCall = MutualRecursiveCall
  { mrcNameFrom :: QName -- ^ The name of the enclosing function where the call is made
  , mrcNameTo :: QName -- ^ The name of the function that is called
  , mrcSizesFrom :: [Int] -- ^ The size context of the enclosing function. In theory it is denoted as Psi_f
  , mrcSizesTo :: [Int] -- ^ The size context of the called function.
  , mrcPlace :: Closure Term -- ^ The place where the call is made
  }

data SizeCheckerState = SizeCheckerState
  { scsMutualNames            :: Set QName
  -- ^ Definitions that are in the current mutual block
  , scsCurrentFunc            :: QName
  -- ^ The function that is checked at the moment
  , scsRecCalls               :: [MutualRecursiveCall]
  -- ^ A set of mutual-recursive calls that are encountered during the process of size checking.
  , scsConstraints            :: [SConstraint]
  -- ^ Lists of edges in the size dependency graph.
  --   This field is local to each clause.
  , scsTotalConstraints       :: [SConstraint]
  -- ^ The list of all constraints during function processing.
  --   This list is global across the function
  , scsRigidSizeVars          :: [(Int, SizeBound)]
  -- ^ Variables that are obtained during the process of pattern matching.
  --   All flexible variables should be expressed as infinity or a rigid variable in the end.
  --   Local to a clause.
  , scsCoreContext            :: [SizeContextEntry]
  -- ^ Size types of the variables from internal syntax.
  --   Local to a clause.
  , scsFreshVarCounter        :: Int
  -- ^ The pool for flexible and rigid variables.
  , scsFreshVarPolarities     :: IntMap Polarity
  -- ^ Association of flexible variables with their polarities. @length scsFreshVarPolarities == scsFreshVarCounter@
  , scsBottomFlexVars         :: IntSet
  -- ^ Flexible variabless that correspond to a non-recursive constructor
  --   The motivation here is that non-recursive constructors (i.e. `zero` of `Nat`) are not bigger than any other term of their type,
  --   so recursive calls with them do not induce undefined order.
  --   In our implementation, we instantiate bottom flexible variables to the minimum of all known leaf rigids.
  , scsLeafSizeVariables       :: [Int]
  -- ^ Rigid size variables that are located at the lowest level of their cluster.
  --   This field is used to assign meaningful sizes to non-recursive constructors,
  --   i.e. the minimum of `scsLeafSizeVariables` is the final expression for size variables variables in `scsBottomFlexVars`.
  --   Populated during the checking of pattern's LHS. The sizes of patterns that are the leaves of the rigid size tree
  , scsFallbackInstantiations :: IntMap Int
  -- ^ Instantiations for a flexible variables, that are used only if it is impossible to know the instantiation otherwise from the graph.
  --   This is the last resort, and a desperate attempt to guess at least something more useful than infinity.
  --   Often this situation happens after projecting a record, where some size variables are simply gone for the later analysis.
  , scsInfiniteVariables     :: IntSet
  -- ^ A set of size variables that have an infinite size as their lower bound.
  --   These sizes are inherently unknown, and we can quickly assign infinity to them during the processing of the graph.
  , scsRecCallsMatrix         :: [[Int]]
  -- ^ When a function calls itself, it becomes a subject of analysis for possible size preservation.
  --   Since we freshen the signatures of all functions that are used in the body,
  --   we can think of a "matrix" of size variables, where the rows correspond to the usages of the same function,
  --   and the columns are freshened versions of the same variable.
  --   During the size preservation, we merge two columns and look at the resulting graph.
  --   Example:
  --   If function `foo : t₀ -> t₁` calls itself, then the call has fresh signature `foo : t₂ -> t₃`, and `scsRecCallsMatrix == [[0, 1], [2, 3]]`
  , scsPreservationCandidates :: IntMap [Int]
  -- ^ A mapping from a variable that can reflect preservation to the possible candidates of preservation.
  --   For example, consider inductive size preservation.
  --   The algorithm of inference starts with each codomain variable being assigned to all domain variables (candidates),
  --   and then clause by clause these candidates are getting refined, i.e. the algorithm prunes the domain variables that certainly cannot appear in a codomain variable.
  , scsErrorMessages          :: [String]
  -- ^ Custom error messages during the process of checking. This is mostly TODO,
  --   because in the current implementation the failure of type-based termination hands the control to syntax-based checker, which will fail with its own errors.
  --   However we still might need to abort type-based termination sometimes,
  --   e.g. a postulated univalence axiom may break the type-based termination checker with an internal error.
  }

getCurrentConstraints :: TBTM [SConstraint]
getCurrentConstraints = TBTM $ gets scsConstraints

getTotalConstraints :: TBTM [SConstraint]
getTotalConstraints = TBTM $ gets scsTotalConstraints

getCurrentRigids :: TBTM [(Int, SizeBound)]
getCurrentRigids = TBTM $ gets scsRigidSizeVars

getCurrentCoreContext :: TBTM [SizeContextEntry]
getCurrentCoreContext = TBTM $ gets scsCoreContext

-- | Initializes internal data strustures that will be filled by the processing of a clause
initNewClause :: [SizeBound] -> TBTM ()
initNewClause bounds = TBTM $ modify (\s -> s
  { scsRigidSizeVars = (zip [0..length bounds] (replicate (length bounds) SizeUnbounded))
  , scsConstraints = [] -- a graph obtained by the processing of a clause corresponds to the clause's rigids
  , scsCoreContext = [] -- like in internal syntax, each clause lives in a separate context
  })

getSizePolarity :: Size -> TBTM Polarity
getSizePolarity SUndefined = pure Invariant
getSizePolarity (SDefined i) = (IntMap.! i) <$> TBTM (gets scsFreshVarPolarities)

storeConstraint :: SConstraint -> TBTM ()
storeConstraint c = TBTM $ modify \ s -> s
  { scsConstraints = c : (scsConstraints s)
  , scsTotalConstraints = c : scsTotalConstraints s
  }

-- | 'reportCall q2 sizes1 sizes2 place' is used to leave a record that there is a call to `q2` with sizes `sizes1` and `sizes2` at the place `place`.
reportCall :: QName -> [Int] -> [Int] -> Closure Term -> TBTM ()
reportCall q2 sizes1 sizes2 place = do
  q1 <- currentCheckedName
  TBTM $ modify (\s -> s
    { scsRecCalls = MutualRecursiveCall
      { mrcNameFrom = q1, mrcNameTo = q2, mrcSizesFrom = sizes1, mrcSizesTo = sizes2, mrcPlace = place
      }
      : scsRecCalls s
    })

setLeafSizeVariables :: [Int] -> TBTM ()
setLeafSizeVariables leaves = TBTM $ modify (\s -> s { scsLeafSizeVariables = leaves })

getLeafSizeVariables :: TBTM [Int]
getLeafSizeVariables = TBTM $ gets scsLeafSizeVariables

currentCheckedName :: TBTM QName
currentCheckedName = TBTM $ gets scsCurrentFunc

getRootArity :: TBTM Int
getRootArity = do
  rootName <- currentCheckedName
  sizeSigArity . defSizedType <$> getConstInfo rootName

currentMutualNames :: TBTM (Set QName)
currentMutualNames = TBTM $ gets scsMutualNames

addFallbackInstantiation :: Int -> Int -> TBTM ()
addFallbackInstantiation i j = TBTM $ modify (\s -> s { scsFallbackInstantiations = IntMap.insert i j (scsFallbackInstantiations s) })

getFallbackInstantiations :: TBTM (IntMap Int)
getFallbackInstantiations = TBTM $ gets scsFallbackInstantiations

-- | Size-preservation machinery needs to know about recursive calls.
-- See the documentation for @scsRecCallsMatrix@
reportDirectRecursion :: [Int] -> TBTM ()
reportDirectRecursion sizes = TBTM $ modify (\s -> s { scsRecCallsMatrix = sizes : scsRecCallsMatrix s })

getRecursionMatrix :: TBTM [[Int]]
getRecursionMatrix = TBTM $ gets scsRecCallsMatrix

-- | 'storeBottomVariable i' is used to leave a record that variable 'i' that is a part of a non-recursive constructor.
storeBottomVariable :: Int -> TBTM ()
storeBottomVariable i = TBTM $ modify (\s -> s { scsBottomFlexVars = IntSet.insert i (scsBottomFlexVars s)})

-- | 'getBottomVariables' returns the set of variables that are part of non-recursive constructors.
getBottomVariables :: TBTM IntSet
getBottomVariables = TBTM $ gets scsBottomFlexVars

-- | 'markInfiniteSize i' is used to mark a size variable as having an infinite lower bound.
markInfiniteSize :: Int -> TBTM ()
markInfiniteSize i = TBTM $ modify (\s -> s { scsInfiniteVariables = IntSet.insert i (scsInfiniteVariables s)})

-- | 'getInfiniteSizes' returns the set of size variables that have an infinite lower bound.
getInfiniteSizes :: TBTM IntSet
getInfiniteSizes = TBTM $ gets scsInfiniteVariables

abstractCoreContext :: Int -> Either FreeGeneric SizeType -> TBTM a -> TBTM a
abstractCoreContext i tele action = do
  contexts <- TBTM $ gets scsCoreContext
  TBTM $ modify \s -> s { scsCoreContext = ((i, tele) : map (incrementDeBruijnEntry tele) contexts) }
  res <- action
  TBTM $ modify \s -> s { scsCoreContext = contexts }
  pure res

incrementDeBruijnEntry :: Either FreeGeneric SizeType -> (Int, Either FreeGeneric SizeType) -> (Int, Either FreeGeneric SizeType)
incrementDeBruijnEntry (Left _) (x, Left fg) = (x + 1, Left $ fg { fgIndex = fgIndex fg + 1 })
incrementDeBruijnEntry (Left _) (x, Right t) = (x + 1, Right t)
incrementDeBruijnEntry (Right _) (x, e) = (x + 1, e)

-- | Performs an action, and returns the result of the action with a number of generated fresh variables.
withVariableCounter :: TBTM a -> TBTM (a, [Int])
withVariableCounter  action = do
  oldCounter <- TBTM $ gets scsFreshVarCounter
  res <- action
  newCounter <- TBTM $ gets scsFreshVarCounter
  pure (res, [oldCounter .. newCounter - 1])

requestNewVariable :: Polarity -> TBTM Int
requestNewVariable pol = TBTM $ do
  x <- gets scsFreshVarCounter
  polarities <- gets scsFreshVarPolarities
  modify (\s -> s
    { scsFreshVarCounter = x + 1
    , scsFreshVarPolarities = IntMap.insert x pol polarities
    })
  return x

-- | 'initSizePreservation candidates replaceable' is used to initialize structures for size preservation.
-- The set of variables that can be size preserving is 'replaceable', and the set of independent variables is 'candidates'
initSizePreservation :: [Int] -> [Int] -> TBTM ()
initSizePreservation candidates replaceable = TBTM $ modify (\s -> s { scsPreservationCandidates = IntMap.fromList $ map (, candidates) (replaceable) })

-- | 'getPreservationCandidates' returns the set of size variables that can be size preserving.
getPreservationCandidates :: TBTM (IntMap [Int])
getPreservationCandidates = TBTM $ gets scsPreservationCandidates

replacePreservationCandidates :: IntMap [Int] -> TBTM ()
replacePreservationCandidates m = TBTM $ modify (\s -> s { scsPreservationCandidates = m })

-- | 'withAnotherPreservationCandidate candidate action' is used to temporarily replace the set of candidates for size preservation.
withAnotherPreservationCandidate :: Int -> TBTM a -> TBTM a
withAnotherPreservationCandidate candidate action = do
  oldState <- TBTM $ gets scsPreservationCandidates
  TBTM $ modify (\s -> s { scsPreservationCandidates = IntMap.insert candidate [] oldState })
  res <- action
  TBTM $ modify (\s -> s { scsPreservationCandidates = oldState })
  pure res

instance Show SConstraint where
  show (SConstraint SLeq i1 i2) = show i1 ++ " ≤ " ++ show i2
  show (SConstraint SLte i1 i2) = show i1 ++ " < " ++ show i2

-- | Given the signature, returns it with with fresh variables
freshenSignature :: Polarity -> SizeSignature -> TBTM ([SConstraint], SizeType)
freshenSignature mainPol s@(SizeSignature domain contra tele) = do
  newVars <- forM ([0 .. length domain - 1]) (\i ->
    let polarity = if List.elem i contra then Contravariant else Covariant
    in requestNewVariable (composePol mainPol polarity))
  let actualConstraints = mapMaybe (\(v, d) -> case d of
                            SizeUnbounded -> Nothing
                            SizeBounded i -> Just (SConstraint SLte v (newVars List.!! i))) (zip newVars domain)
      sigWithfreshenedSizes = updateSizeVariables (newVars List.!!) tele
  -- freshSig <- freshenGenericArguments sigWithfreshenedSizes
  let newContravariantVariables = map (newVars List.!!) contra
  return $ (actualConstraints, sigWithfreshenedSizes)

requestNewRigidVariable :: Polarity -> SizeBound -> TBTM Int
requestNewRigidVariable pol bound = do
  newVarIdx <- requestNewVariable pol
  TBTM $ do
    currentRigids <- gets scsRigidSizeVars
    modify \s -> s { scsRigidSizeVars = ((newVarIdx, bound) : currentRigids) }
    return newVarIdx

appendCoreVariable :: Int -> Either FreeGeneric SizeType -> TBTM ()
appendCoreVariable i tele = TBTM $ modify \s -> s { scsCoreContext = ((i, tele) : (scsCoreContext s)) }

recordError :: String -> TBTM ()
recordError msg = TBTM $ modify (\s -> s { scsErrorMessages = msg : scsErrorMessages s })

-- | Due to limitations of the theory behind the type-based checker,
--   certain syntactic constructions are not supported in the inference process.
--   To prevent possible unsoundness, we purposefully fail the checker when such constructions are encountered.
hasEncodingErrors :: TBTM Bool
hasEncodingErrors = TBTM $ gets (not . null . scsErrorMessages)

runSizeChecker :: QName -> Set QName -> TBTM a -> TCM (a, [SConstraint], [String], [MutualRecursiveCall])
runSizeChecker rootName mutualNames (TBTM action) = do
  (res, finalState) <- runStateT action
    (SizeCheckerState
    { scsMutualNames = mutualNames
    , scsCurrentFunc = rootName
    , scsRecCalls = []
    , scsConstraints = []
    , scsTotalConstraints = []
    , scsRigidSizeVars = []
    , scsFreshVarCounter = 0
    , scsFreshVarPolarities = IntMap.empty
    , scsCoreContext = []
    , scsBottomFlexVars = IntSet.empty
    , scsLeafSizeVariables = []
    , scsFallbackInstantiations = IntMap.empty
    , scsInfiniteVariables = IntSet.empty
    , scsRecCallsMatrix = []
    , scsPreservationCandidates = IntMap.empty
    , scsErrorMessages = []
    })
  pure (res, scsConstraints finalState, scsErrorMessages finalState, scsRecCalls finalState)
