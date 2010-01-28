-- | Call graphs and related concepts, more or less as defined in
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch.

-- Originally copied from Agda1 sources.

module Agda.Termination.CallGraph
  ( -- * Structural orderings
    Order(..)
  , (.*.)
  , supremum
    -- * Call matrices
  , Index
  , CallMatrix(..)
  , (>*<)
  , callMatrixInvariant
    -- * Calls
  , Call(..)
  , callInvariant
    -- * Call graphs
  , CallGraph
  , callGraphInvariant
  , fromList
  , toList
  , empty
  , union
  , insert
  , complete
  , showBehaviour
    -- * Tests
  , Agda.Termination.CallGraph.tests
  ) where

import Agda.Utils.QuickCheck
import Agda.Utils.Function
import Agda.Utils.List
import Agda.Utils.TestHelpers
import Agda.Termination.SparseMatrix as Matrix
import Agda.Termination.Semiring (Semiring)
import qualified Agda.Termination.Semiring as Semiring
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.List hiding (union, insert)
import Data.Monoid
import Data.Array (elems)
import Data.Function

------------------------------------------------------------------------
-- Structural orderings

-- | The order called R in the paper referred to above. Note that
-- @'Unknown' '<=' 'Le' '<=' 'Lt'@.
--
-- See 'Call' for more information.
--
-- TODO: document orders which are call-matrices themselves.
data Order
  = Lt | Le | Unknown | Mat (Matrix Integer Order)
  deriving (Eq,Ord)

instance Show Order where
  show Lt      = "<"
  show Le      = "="
  show Unknown = "?"
  show (Mat m) = "Mat " ++ show m

--instance Ord Order where
--    max = maxO

instance Arbitrary Order where
  arbitrary = elements [Lt, Le, Unknown]

instance CoArbitrary Order where
  coarbitrary Lt      = variant 0
  coarbitrary Le      = variant 1
  coarbitrary Unknown = variant 2
  coarbitrary (Mat m) = variant 3

-- | Multiplication of 'Order's. (Corresponds to sequential
-- composition.)

(.*.) :: Order -> Order -> Order
Lt      .*. Unknown   = Unknown
Lt      .*. (Mat m)   = Lt .*. collapse m
Lt      .*. _         = Lt
Le      .*. o         = o
Unknown .*. _         = Unknown
(Mat m1) .*. (Mat m2) = if okM m1 m2 then
                            Mat (mul m1 m2)
                        else
                            collapse m1 .*. collapse m2
(Mat m) .*. Le        = Mat m
(Mat m) .*. Unknown   = Unknown
(Mat m) .*. Lt        = collapse m .*. Lt

collapse :: Matrix Integer Order -> Order
collapse m = foldl (.*.) Le (Data.Array.elems $ diagonal m)

okM :: Matrix Integer Order -> Matrix Integer Order -> Bool
okM m1 m2 = (rows $ size m2) == (cols $ size m1)

-- | The supremum of a (possibly empty) list of 'Order's.

supremum :: [Order] -> Order
supremum = foldr maxO Unknown

maxO :: Order -> Order -> Order
maxO o1 o2 = case (o1,o2) of
               (_,Lt) -> Lt
               (Lt,_) -> Lt
               (Unknown,_) -> o2
               (_,Unknown) -> o1
               (Mat m1, Mat m2) -> Mat (Matrix.add maxO m1 m2)
               (Mat m,_) -> maxO (collapse m) o2
               (_,Mat m) ->  maxO o1 (collapse m)
               (Le,Le) -> Le

-- | @('Order', 'max', '.*.')@ forms a semiring, with 'Unknown' as
-- zero and 'Le' as one.

instance Semiring Order where
  add  = maxO
  mul  = (.*.)
  zero = Unknown
  one  = Le

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

instance CoArbitrary CallMatrix where
  coarbitrary (CallMatrix m) = coarbitrary m

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
-- Precondition: see 'Matrix.mul'.

(<*>) :: CallMatrix -> CallMatrix -> CallMatrix
cm1 <*> cm2 = CallMatrix { mat = mul (mat cm1) (mat cm2) }

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
  Call { source :: Index        -- ^ The function making the call.
       , target :: Index        -- ^ The function being called.
       , cm :: CallMatrix       -- ^ The call matrix describing the call.
       }
  deriving (Eq, Ord, Show)

instance Arbitrary Call where
  arbitrary = do
    [s, t]    <- vectorOf 2 arbitrary
    cm        <- arbitrary
    return (Call { source = s, target = t, cm = cm })

instance CoArbitrary Call where
  coarbitrary (Call s t cm) =
    coarbitrary s . coarbitrary t . coarbitrary cm

-- | 'Call' invariant.

callInvariant :: Call -> Bool
callInvariant = callMatrixInvariant . cm

-- | 'Call' combination.
--
-- Precondition: see '<*>'; furthermore the 'source' of the first
-- argument should be equal to the 'target' of the second one.

(>*<) :: Call -> Call -> Call
c1 >*< c2 =
  Call { source    = source c2
       , target    = target c1
       , cm        = cm c1 <*> cm c2
       }

------------------------------------------------------------------------
-- Call graphs

-- | A call graph is a set of calls. Every call also has some
-- associated meta information, which should be 'Monoid'al so that the
-- meta information for different calls can be combined when the calls
-- are combined.

newtype CallGraph meta = CallGraph { cg :: Map Call meta }
  deriving (Eq, Show)

-- | 'CallGraph' invariant.

callGraphInvariant :: CallGraph meta -> Bool
callGraphInvariant = all (callInvariant . fst) . toList

-- | Converts a call graph to a list of calls with associated meta
-- information.

toList :: CallGraph meta -> [(Call, meta)]
toList = Map.toList . cg

-- | Converts a list of calls with associated meta information to a
-- call graph.

fromList :: Monoid meta => [(Call, meta)] -> CallGraph meta
fromList = CallGraph . Map.fromListWith mappend

-- | Creates an empty call graph.

empty :: CallGraph meta
empty = CallGraph Map.empty

-- | Takes the union of two call graphs.

union :: Monoid meta
      => CallGraph meta -> CallGraph meta -> CallGraph meta
union cs1 cs2 = CallGraph $ (Map.unionWith mappend `on` cg) cs1 cs2

-- | Inserts a call into a call graph.

insert :: Monoid meta
       => Call -> meta -> CallGraph meta -> CallGraph meta
insert c m = CallGraph . Map.insertWith mappend c m . cg

-- | Generates a call graph.

callGraph :: (Monoid meta, Arbitrary meta) => Gen (CallGraph meta)
callGraph = do
  indices <- fmap nub arbitrary
  n <- natural
  let noMatrices | null indices = 0
                 | otherwise    = n `min` 3  -- Not too many.
  fmap fromList $ vectorOf noMatrices (matGen indices)
  where
  matGen indices = do
    [s, t] <- vectorOf 2 (elements indices)
    [c, r] <- vectorOf 2 (choose (0, 2))     -- Not too large.
    m <- callMatrix (Size { rows = r, cols = c })
    callId <- arbitrary
    return (Call { source = s, target = t, cm = m }, callId)

prop_callGraph =
  forAll (callGraph :: Gen (CallGraph [Integer])) $ \cs ->
    callGraphInvariant cs

-- | Call graph combination. (Application of '>*<' to all pairs @(c1,
-- c2)@ for which @'source' c1 = 'target' c2@.)
--
-- Precondition: see '<*>'.

combine
  :: Monoid meta => CallGraph meta -> CallGraph meta -> CallGraph meta
combine s1 s2 = fromList $
  [ (c1 >*< c2, m1 `mappend` m2)
  | (c1, m1) <- toList s1, (c2, m2) <- toList s2
  , source c1 == target c2
  ]

-- | @'complete' cs@ completes the call graph @cs@. A call graph is
-- complete if it contains all indirect calls; if @f -> g@ and @g ->
-- h@ are present in the graph, then @f -> h@ should also be present.

complete :: Monoid meta => CallGraph meta -> CallGraph meta
complete cs = complete' safeCS
  where
  safeCS = ensureCompletePrecondition cs

  complete' cs | cs' .==. cs = cs
               | otherwise   = complete' cs'
    where
    cs' = cs `union` combine cs safeCS
    (.==.) = ((==) `on` (Map.keys . cg))

prop_complete =
  forAll (callGraph :: Gen (CallGraph [Integer])) $ \cs ->
    isComplete (complete cs)

-- | Returns 'True' iff the call graph is complete.

isComplete :: (Ord meta, Monoid meta) => CallGraph meta -> Bool
isComplete s = all (`Map.member` cg s) combinations
  where
  calls = toList s
  combinations =
    [ c2 >*< c1 | (c1, _) <- calls, (c2, _) <- calls
                , target c1 == source c2 ]

-- | Checks whether every 'Index' used in the call graph corresponds
-- to a fixed number of arguments (i.e. rows\/columns).

completePrecondition :: CallGraph meta -> Bool
completePrecondition cs =
  all (allEqual . map snd) $
  groupOn fst $
  concat [ [(source c, cols $ size' c), (target c, rows $ size' c)]
         | (c, _) <- toList cs]
  where
  size' = size . mat . cm

-- | Returns a call graph padded with 'Unknown's in such a way that
-- 'completePrecondition' is satisfied.

ensureCompletePrecondition
  :: Monoid meta => CallGraph meta -> CallGraph meta
ensureCompletePrecondition cs =
  CallGraph $ Map.mapKeysWith mappend pad $ cg cs
  where
  -- The maximum number of arguments detected for every index.
  noArgs :: Map Index Integer
  noArgs = foldr (\c m -> insert (source c) (cols' c) $
                          insert (target c) (rows' c) m)
                 Map.empty
                 (map fst $ toList cs)
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
    all callInvariant (map fst $ toList cs')
    &&
    and [ or [ new .==. old | (old, _) <- toList cs ]
        | (new, _) <- toList cs' ]
  where
  c1 .==. c2 = all (all (uncurry (==)))
                   ((zipZip `on` (toLists . mat . cm)) c1 c2)

  -- zipZip discards the new elements.
  zipZip :: [[a]] -> [[b]] -> [[(a, b)]]
  zipZip xs ys = map (uncurry zip) $ zip xs ys

-- | Displays the recursion behaviour corresponding to a call graph.

showBehaviour :: Show meta => CallGraph meta -> String
showBehaviour = concatMap showCall . toList
  where
  showCall (c, meta) | source c /= target c = ""
                     | otherwise            = unlines
    [ "Function:  " ++ show (source c)
    , "Behaviour: " ++ show (elems $ diagonal $ mat $ cm c)
    , "Meta info: " ++ show meta
    ]

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.CallGraph"
  [ quickCheck' (Semiring.semiringInvariant
                   :: Order -> Order -> Order -> Bool)
  , quickCheck' callMatrixInvariant
  , quickCheck' prop_callMatrix
  , quickCheck' prop_cmMul
  , quickCheck' callInvariant
  , quickCheck' prop_callGraph
  , quickCheck' prop_complete
  , quickCheck' prop_ensureCompletePrecondition
  ]
