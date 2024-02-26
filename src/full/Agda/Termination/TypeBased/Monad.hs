module Agda.Termination.TypeBased.Monad where

import Control.Monad.Trans.State ( StateT, gets, modify, runStateT )
import Agda.TypeChecking.Monad.Base ( TCM, pattern Function, funTerminates, FunctionData (..), pattern Datatype, pattern Record, recInduction, Reduced (..), liftTCM, theDef, defType, defSizedType, defCopy, defIsDataOrRecord, MonadTCEnv, MonadTCState, HasOptions, Closure, MonadTCM, ReadTCState )
import Agda.TypeChecking.Monad.Debug ( MonadDebug, reportSDoc )
import Agda.TypeChecking.Monad.Signature ( getConstInfo, HasConstInfo, usesCopatterns )
import Agda.TypeChecking.Monad.Context ( MonadAddContext )
import qualified Data.Map as Map
import Data.Map ( Map)
import qualified Data.IntMap as IntMap
import Data.IntMap ( IntMap )
import qualified Data.IntSet as IntSet
import Data.IntSet ( IntSet )
import Control.Monad.IO.Class ( MonadIO )
import qualified Data.List as List
import Agda.Syntax.Abstract.Name ( QName )
import Agda.Termination.TypeBased.Syntax
import Agda.Syntax.Internal ( Term (..), unEl, unAbs, unDom, Dom, Abs(..), Sort, MetaId(..), isApplyElim )
import Agda.TypeChecking.Monad.Statistics ( MonadStatistics )
import Agda.Termination.TypeBased.Common

import Agda.TypeChecking.Pretty
import Control.Arrow ( first )
import Control.Monad
import Data.Maybe
import Data.Set (Set )

import Agda.Utils.Impossible

import qualified Agda.Utils.Benchmark as B
import qualified Agda.Benchmarking as Benchmark

import qualified Agda.Syntax.Common.Pretty as P

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
  , MonadFail
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

data SizeCheckerState = SizeCheckerState
  { scsMutualNames            :: Set QName
  -- ^ Definitions that are in the current mutual block
  , scsCurrentFunc            :: QName
  -- ^ The function that is checked at the moment
  , scsRecCalls               :: [(QName, QName, [Int], [Int], Closure Term)]
  -- ^ [(f, g, Psi_f, Psi_g, place)], where Psi is the representation of the size context (see Abel & Pientka 2016)
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
  -- ^ A counter that represents a pool of new first-order size variables. Both rigid and flexible variables are taken from this pool.
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
  , scsContravariantVariables :: IntSet
  -- ^ Size variables that belong to coinductive definitions.
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

isContravariant :: Size -> TBTM Bool
isContravariant SUndefined = pure False
isContravariant (SDefined i) = do
  IntSet.member i <$> TBTM (gets scsContravariantVariables)

getContravariantSizeVariables :: TBTM IntSet
getContravariantSizeVariables = TBTM $ gets scsContravariantVariables

recordContravariantSizeVariable :: Int -> TBTM ()
recordContravariantSizeVariable i = TBTM $ modify (\s -> s { scsContravariantVariables = IntSet.insert i (scsContravariantVariables s) })

-- | Retrieves the number of size variables in the sized signature of @qn@
getArity :: QName -> TBTM Int
getArity qn = sizeSigArity . fromJust . defSizedType <$> getConstInfo qn

storeConstraint :: SConstraint -> TBTM ()
storeConstraint c = TBTM $ modify \ s -> s
  { scsConstraints = c : (scsConstraints s)
  , scsTotalConstraints = c : scsTotalConstraints s
  }

reportCall :: QName -> QName -> [Int] -> [Int] -> Closure Term -> TBTM ()
reportCall q1 q2 sizes1 sizes2 place = TBTM $ modify (\s -> s { scsRecCalls = (q1, q2, sizes1, sizes2, place) : scsRecCalls s })

setLeafSizeVariables :: [Int] -> TBTM ()
setLeafSizeVariables leaves = TBTM $ modify (\s -> s { scsLeafSizeVariables = leaves })

getLeafSizeVariables :: TBTM [Int]
getLeafSizeVariables = TBTM $ gets scsLeafSizeVariables

currentCheckedName :: TBTM QName
currentCheckedName = TBTM $ gets scsCurrentFunc

getRootArity :: TBTM Int
getRootArity = do
  rootName <- currentCheckedName
  getArity rootName

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

requestNewVariable :: TBTM Int
requestNewVariable = TBTM $ do
  x <- gets scsFreshVarCounter
  modify (\s -> s { scsFreshVarCounter = (x + 1) })
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
freshenSignature :: SizeSignature -> TBTM ([SConstraint], SizeType)
freshenSignature s@(SizeSignature domain contra tele) = do
  -- reportSDoc "term.tbt" 10 $ "Signature to freshen: " <+> text (show s)
  newVars <- replicateM (length domain) requestNewVariable
  let actualConstraints = mapMaybe (\(v, d) -> case d of
                            SizeUnbounded -> Nothing
                            SizeBounded i -> Just (SConstraint SLte v (newVars List.!! i))) (zip newVars domain)
      sigWithfreshenedSizes = instantiateSizeType tele newVars
  -- freshSig <- freshenGenericArguments sigWithfreshenedSizes
  let newContravariantVariables = map (newVars List.!!) contra
  TBTM $ modify ( \s -> s { scsContravariantVariables = foldr IntSet.insert (scsContravariantVariables s) newContravariantVariables  })
  return $ (actualConstraints, sigWithfreshenedSizes)

-- | Instantiates first order size variables to the provided list of ints
instantiateSizeType :: SizeType -> [Int] -> SizeType
instantiateSizeType body args = update (\i -> args List.!! i) body

requestNewRigidVariable :: SizeBound -> TBTM Int
requestNewRigidVariable bound = do
  newVarIdx <- requestNewVariable
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

runSizeChecker :: QName -> Set QName -> TBTM a -> TCM (a, SizeCheckerState)
runSizeChecker rootName mutualNames (TBTM action) = do
  runStateT action
    (SizeCheckerState
    { scsMutualNames = mutualNames
    , scsCurrentFunc = rootName
    , scsRecCalls = []
    , scsConstraints = []
    , scsTotalConstraints = []
    , scsRigidSizeVars = []
    , scsFreshVarCounter = 0
    , scsCoreContext = []
    , scsBottomFlexVars = IntSet.empty
    , scsLeafSizeVariables = []
    , scsContravariantVariables = IntSet.empty
    , scsFallbackInstantiations = IntMap.empty
    , scsInfiniteVariables = IntSet.empty
    , scsRecCallsMatrix = []
    , scsPreservationCandidates = IntMap.empty
    , scsErrorMessages = []
    })
