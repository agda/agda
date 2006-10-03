-- | Call graphs and related concepts, more or less as defined in
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch.

-- Originally copied from Agda1 sources.

module Termination.CallGraph
  ( Order(..)
  , Index
  , CallMatrix(..)
  , callMatrixInvariant
  , Call(..)
  , callInvariant
  , CallGraph
  , complete
  , completePrecondition
  ) where

import Test.QuickCheck
import Termination.TestHelpers
import Termination.Utilities
import Termination.Matrix
import Termination.Semiring (Semiring)
import qualified Termination.Semiring as Semiring
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List

------------------------------------------------------------------------
-- Structural orderings

-- | The order called R in the paper referred to above.
--
-- See 'Call' for more information.

data Order
  = Lt | Le | Unknown
  deriving (Eq, Ord, Show)

instance Arbitrary Order where
  arbitrary = elements [Lt, Le, Unknown]

  coarbitrary Lt      = variant 0
  coarbitrary Le      = variant 1
  coarbitrary Unknown = variant 2

-- | Addition of 'Order's.

(.+.) :: Order -> Order -> Order
Lt      .+. _  = Lt
Le      .+. Lt = Lt
Le      .+. _  = Le
Unknown .+. o  = o

-- | Multiplication of 'Order's.

(.*.) :: Order -> Order -> Order
Lt      .*. Unknown = Unknown
Lt      .*. _       = Lt
Le      .*. o       = o
Unknown .*. _       = Unknown

-- | @('Order', '.+.', '.*.')@ forms a semiring, with 'Unknown' as zero
-- and 'Le' as one.

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

data Call =
  Call { source :: Index   -- ^ The function making the call.
       , target :: Index   -- ^ The function being called.
       , cm :: CallMatrix  -- ^ The call matrix describing the call.
       }
  deriving (Eq, Ord, Show)

instance Arbitrary Call where
  arbitrary = do
    (s, t) <- two arbitrary
    cm     <- arbitrary
    return (Call { source = s, target = t, cm = cm })

  coarbitrary (Call s t cm) =
    coarbitrary s . coarbitrary t . coarbitrary cm

prop_Arbitrary_Call = callInvariant

-- | 'Call' invariant.

callInvariant :: Call -> Bool
callInvariant = callMatrixInvariant . cm

-- | Call combination.
--
-- Precondition: see '<*>'; furthermore the 'source' of the first
-- argument should be equal to the 'target' of the second one.

(>*<) :: Call -> Call -> Call
c1 >*< c2 =
  Call { source = source c2, target = target c1, cm = cm c1 <*> cm c2 }

------------------------------------------------------------------------
-- Call graphs

-- | A call graph is a set of calls.

type CallGraph = Set Call

-- | Generates a call set satisfying 'completePrecondition'.

callGraph :: Gen (CallGraph)
callGraph = do
  indices <- fmap nub arbitrary
  lengths <- listOfLength (length indices) (choose (0, 3))  -- Not too large.
  let indexMap = zip indices lengths
  n <- natural :: Gen Integer
  let noMatrices | null indexMap = 0
                 | otherwise     = n `max` 3  -- Not too many.
  fmap Set.fromList $ listOfLength noMatrices (matGen indexMap)
  where
  matGen indexMap = do
    ((s, c), (t, r)) <- two (elements indexMap)
    m <- matrix (Size { rows = r, cols = c })
    return $ Call { source = s, target = t
                  , cm = CallMatrix { mat = m } }

prop_callGraph =
  forAll callGraph $ \cs ->
    completePrecondition cs

-- | Call graph combination. (Application of '>*<' to all pairs @(c1,
-- c2)@ for which @'source' c1 = 'target' c2@.)
--
-- Precondition: see '<*>'.

combine :: CallGraph -> CallGraph -> CallGraph
combine s1 s2 =
  Set.fromList [ c1 >*< c2
               | c1 <- Set.toList s1, c2 <- Set.toList s2
               , source c1 == target c2
               ]

-- | @'complete' cs@ completes the call graph @cs@. A call graph is
-- complete if it contains all indirect calls; if @f -> g@ and @g ->
-- h@ are present in the graph, then @f -> h@ should also be present.
--
-- Precondition: @'completePrecondition' cs@.

complete :: CallGraph -> CallGraph
complete c = complete' c
  where
  complete' cs | cs' == cs = cs
               | otherwise = complete' cs'
    where cs' = Set.union cs (combine cs c)

prop_complete =
  forAll callGraph $ \cs ->
    isComplete (complete cs)

-- | Returns 'True' iff the call graph is complete.

isComplete :: CallGraph -> Bool
isComplete s = all (`Set.member` s) combinations
  where
  calls = Set.toList s
  combinations =
    [ c2 >*< c1 | c1 <- calls, c2 <- calls, target c1 == source c2 ]

-- | Checks whether every 'Index' used in the call graph corresponds
-- to a fixed number of arguments (i.e. rows\/columns).

completePrecondition :: CallGraph -> Bool
completePrecondition cs =
  all (allEqual . map snd) $
  groupOn fst $
  concat [ [(source c, cols $ size' c), (target c, rows $ size' c)]
         | c <- Set.toList cs]
  where
  size' = size . mat . cm

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
