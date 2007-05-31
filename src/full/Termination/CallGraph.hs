-- | Call graphs and related concepts, more or less as defined in
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch.

-- Originally copied from Agda1 sources.

module Termination.CallGraph
  ( Order(..)
  , (.*.)
  , infimum
  , supremum
  , Index
  , CallMatrix(..)
  , callMatrixInvariant
  , Call(..)
  , callInvariant
  , CallGraph
  , callGraphInvariant
  , emptyCallGraph   
  , unionCallGraphs
  , insertCallGraph
  , complete
  , Termination.CallGraph.tests
  ) where

import Test.QuickCheck
import Utils.Function hiding (on)
import Utils.TestHelpers
import Termination.Utilities
import Termination.Matrix
import Termination.Semiring (Semiring)
import qualified Termination.Semiring as Semiring
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.List
import Data.Monoid

------------------------------------------------------------------------
-- Structural orderings

-- | The order called R in the paper referred to above.
--
-- See 'Call' for more information.

data Order
  = Lt | Le | Unknown
  deriving (Eq, Show)

{- | Information order.  'Unknown' <= 'Le' <= 'Lt'.
     The bigger the element of 'Order' the smaller, hence, more informative, 
     the order between values it represents.
-}

instance Ord Order where
  _       <= Lt = True
  Unknown <= _  = True
  Le      <= Le = True
  _       <= _  = False

instance Arbitrary Order where
  arbitrary = elements [Lt, Le, Unknown]

  coarbitrary Lt      = variant 0
  coarbitrary Le      = variant 1
  coarbitrary Unknown = variant 2

{- | Addition of 'Order's.  This coincides with the supremum.  
The neutral (and bottom) element is 'Unknown'. -}

(.+.) :: Order -> Order -> Order
(.+.) = max

{-
(.+.) :: Order -> Order -> Order
Lt      .+. _  = Lt
Le      .+. Lt = Lt
Le      .+. _  = Le
Unknown .+. o  = o
-}

{- | Multiplication of 'Order's.  Sequential composition.  
The neutral element is 'Le'. -}

(.*.) :: Order -> Order -> Order
Lt      .*. Unknown = Unknown
Lt      .*. _       = Lt
Le      .*. o       = o
Unknown .*. _       = Unknown

-- | @('Order', '.+.', '.*.')@ forms a semiring, with 'Unknown' as zero
-- and 'Le' as one.  

-- | 'supremum' works also for empty lists (unlike 'List.maximum').
supremum :: [Order] -> Order
supremum = foldl max Unknown

-- | 'infimum' works also for empty lists (unlike 'List.maximum').
infimum :: [Order] -> Order
infimum = foldl min Lt

orderSemiring :: Semiring Order
orderSemiring =
  Semiring.Semiring { Semiring.add = (.+.), Semiring.mul = (.*.)
                    , Semiring.zero = Unknown, Semiring.one = Le}

prop_orderSemiring = Semiring.semiringInvariant orderSemiring

------------------------------------------------------------------------
-- Call matrices

-- | Call matrix indices.

type Index = Integer

-- | Call matrices. Note the call matrix invariant
-- ('callMatrixInvariant').

newtype CallMatrix = CallMatrix { mat :: Matrix Index Order }
  deriving (Eq, Ord, Show)

instance Arbitrary CallMatrix where
  arbitrary = do
    sz <- arbitrary
    callMatrix sz

  coarbitrary (CallMatrix m) = coarbitrary m

prop_Arbitrary_CallMatrix = callMatrixInvariant

-- | Generates a call matrix of the given size.

callMatrix :: Size Index -> Gen CallMatrix
callMatrix sz = do
  m <- matrixUsingRowGen sz rowGen
  return $ CallMatrix { mat = m }
  where
  rowGen :: Index -> Gen [Order]
  rowGen 0 = return []
  rowGen n = do
    x <- arbitrary
    i <- choose (0, n - 1)
    return $ genericReplicate i Unknown ++ [x] ++
             genericReplicate (n - 1 - i) Unknown

prop_callMatrix sz =
  forAll (callMatrix sz) $ \cm ->
    callMatrixInvariant cm
    &&
    size (mat cm) == sz

-- | In a call matrix at most one element per row may be different
-- from 'Unknown'.

callMatrixInvariant :: CallMatrix -> Bool
callMatrixInvariant cm =
  matrixInvariant m &&
  all ((<= 1) . length . filter (/= Unknown)) (toLists m)
  where m = mat cm

-- | Call matrix multiplication.
--
-- Precondition: see 'mul'.

(<*>) :: CallMatrix -> CallMatrix -> CallMatrix
cm1 <*> cm2 =
  CallMatrix { mat = mul orderSemiring (mat cm1) (mat cm2) }

prop_cmMul sz =
  forAll natural $ \c2 ->
  forAll (callMatrix sz) $ \cm1 ->
  forAll (callMatrix $ Size { rows = cols sz, cols = c2 }) $ \cm2 ->
    callMatrixInvariant (cm1 <*> cm2)

------------------------------------------------------------------------
-- Calls

-- | This datatype encodes information about a single recursive
-- function application. The columns of the call matrix stand for
-- 'source' function arguments (patterns); the first argument has
-- index 0, the second 1, and so on. The rows of the matrix stand for
-- 'target' function arguments. Element @(i, j)@ in the matrix should
-- be computed as follows:
--
--   * 'Lt' (less than) if the @j@-th argument to the 'target'
--     function is structurally strictly smaller than the @i@-th
--     pattern.
--
--   * 'Le' (less than or equal) if the @j@-th argument to the
--     'target' function is structurally smaller than the @i@-th
--     pattern.
--
--   * 'Unknown' otherwise.
--
--   The structural ordering used is defined in the paper referred to
--   above.

data Call call =
  Call { source :: Index   -- ^ The function making the call.
       , target :: Index   -- ^ The function being called.
       , callId :: call    -- ^ An identifier for this particular call. 
                           --   This identifier is not used when
                           --   comparing calls in the 'Eq' and 'Ord'
                           --   instances.
       , cm :: CallMatrix  -- ^ The call matrix describing the call.
       }
  deriving Show

callInfo c = (source c, target c, cm c)

instance Eq (Call call) where
  (==) = (==) `on` callInfo

instance Ord (Call call) where
  compare = compare `on` callInfo

instance Arbitrary call => Arbitrary (Call call) where
  arbitrary = do
    (s, t) <- two arbitrary
    cm     <- arbitrary
    callId <- arbitrary
    return (Call { source = s, target = t, callId = callId, cm = cm })

  coarbitrary (Call s t callId cm) =
    coarbitrary s . coarbitrary t . coarbitrary callId . coarbitrary cm

prop_Arbitrary_Call :: Call Integer -> Bool
prop_Arbitrary_Call = callInvariant

-- | 'Call' invariant.

callInvariant :: Call call -> Bool
callInvariant = callMatrixInvariant . cm

-- | 'Call' combination. The 'callId's are combined using the monoid.
--
-- Precondition: see '<*>'; furthermore the 'source' of the first
-- argument should be equal to the 'target' of the second one.

(>*<) :: Monoid call => Call call -> Call call -> Call call
c1 >*< c2 =
  Call { source = source c2, target = target c1
       , callId = callId c2 `mappend` callId c1
       , cm = cm c1 <*> cm c2 }

------------------------------------------------------------------------
-- Call graphs

-- | A call graph is a set of calls.

type CallGraph call = Set (Call call)

-- | 'CallGraph' invariant.

callGraphInvariant :: CallGraph call -> Bool
callGraphInvariant = all callInvariant . Set.toList

emptyCallGraph :: CallGraph call
emptyCallGraph = Set.empty

sgCallGraph :: Call call -> CallGraph call
sgCallGraph = Set.singleton

unionCallGraphs :: CallGraph call -> CallGraph call -> CallGraph call
unionCallGraphs = Set.union

insertCallGraph :: Call call -> CallGraph call -> CallGraph call
insertCallGraph = Set.insert

-- | Generates a call set.

callGraph :: (Ord call, Arbitrary call) => Gen (CallGraph call)
callGraph = do
  indices <- fmap nub arbitrary
  n <- natural :: Gen Integer
  let noMatrices | null indices = 0
                 | otherwise    = n `max` 3  -- Not too many.
  fmap Set.fromList $ listOfLength noMatrices (matGen indices)
  where
  matGen indices = do
    (s, t) <- two (elements indices)
    (c, r) <- two (choose (0, 2))     -- Not too large.
    m <- callMatrix (Size { rows = r, cols = c })
    callId <- arbitrary
    return $ Call { source = s, target = t, callId = callId, cm = m }

prop_callGraph =
  forAll (callGraph :: Gen (CallGraph Integer)) $ \cs ->
    callGraphInvariant cs

-- | Call graph combination. (Application of '>*<' to all pairs @(c1,
-- c2)@ for which @'source' c1 = 'target' c2@.)
--
-- Precondition: see '<*>'.

combine :: (Ord call, Monoid call)
        => CallGraph call -> CallGraph call -> CallGraph call
combine s1 s2 =
  Set.fromList [ c1 >*< c2
               | c1 <- Set.toList s1, c2 <- Set.toList s2
               , source c1 == target c2
               ]

-- | @'complete' cs@ completes the call graph @cs@. A call graph is
-- complete if it contains all indirect calls; if @f -> g@ and @g ->
-- h@ are present in the graph, then @f -> h@ should also be present.

complete :: (Ord call, Monoid call) => CallGraph call -> CallGraph call
complete cs = complete' safeCS
  where
  safeCS = ensureCompletePrecondition cs

  complete' cs | cs' == cs = cs
               | otherwise = complete' cs'
    where cs' = Set.union cs (combine cs safeCS)

prop_complete =
  forAll (callGraph :: Gen (CallGraph [Integer])) $ \cs ->
    isComplete (complete cs)

-- | Returns 'True' iff the call graph is complete.

isComplete :: (Ord call, Monoid call) => CallGraph call -> Bool
isComplete s = all (`Set.member` s) combinations
  where
  calls = Set.toList s
  combinations =
    [ c2 >*< c1 | c1 <- calls, c2 <- calls, target c1 == source c2 ]

-- | Checks whether every 'Index' used in the call graph corresponds
-- to a fixed number of arguments (i.e. rows\/columns).

completePrecondition :: CallGraph call -> Bool
completePrecondition cs =
  all (allEqual . map snd) $
  groupOn fst $
  concat [ [(source c, cols $ size' c), (target c, rows $ size' c)]
         | c <- Set.toList cs]
  where
  size' = size . mat . cm

-- | Returns a call graph padded with 'Unknown's in such a way that
-- 'completePrecondition' is satisfied.

ensureCompletePrecondition :: CallGraph call -> CallGraph call
ensureCompletePrecondition cs = Set.map pad cs
  where
  noArgs :: Map Index Integer
  noArgs = Set.fold (\c m -> insert (source c) (cols' c) $
                             insert (target c) (rows' c) m)
                    Map.empty
                    cs
    where insert = Map.insertWith max

  pad c = c { cm = CallMatrix { mat = padRows $ padCols $ mat $ cm c } }
    where
    padCols = iterate' ((noArgs ! source c) - cols' c)
                       (addColumn Unknown)

    padRows = iterate' ((noArgs ! target c) - rows' c)
                       (addRow Unknown)

  cols'  = cols . size'
  rows'  = rows . size'
  size'  = size . mat . cm

prop_ensureCompletePrecondition =
  forAll (callGraph :: Gen (CallGraph [Integer])) $ \cs ->
    let cs' = ensureCompletePrecondition cs in
    completePrecondition cs'
    &&
    all callInvariant (Set.toList cs')
    &&
    and [ or [ new .==. old | old <- Set.toAscList cs ]
        | new <- Set.toAscList cs' ]
  where
  c1 .==. c2 = all (all (uncurry (==)))
                   ((zipZip `on` (toLists . mat . cm)) c1 c2)

  -- zipZip discards the new elements.
  zipZip :: [[a]] -> [[b]] -> [[(a, b)]]
  zipZip xs ys = map (uncurry zip) $ zip xs ys

------------------------------------------------------------------------
-- All tests

tests = do
  quickCheck prop_orderSemiring
  quickCheck prop_Arbitrary_CallMatrix
  quickCheck prop_callMatrix
  quickCheck prop_cmMul
  quickCheck prop_Arbitrary_Call
  quickCheck prop_callGraph
  quickCheck prop_complete
  quickCheck prop_ensureCompletePrecondition
