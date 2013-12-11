{-# LANGUAGE CPP, ImplicitParams, TypeSynonymInstances, FlexibleInstances,
  GeneralizedNewtypeDeriving, StandaloneDeriving, DeriveFunctor,
  DeriveFoldable, DeriveTraversable #-}

-- | Call graphs and related concepts, more or less as defined in
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch.

-- Originally copied from Agda1 sources.

module Agda.Termination.CallGraph
  ( -- * Structural orderings
    Order(Mat), decr
  , increase, decrease
  , (.*.)
  , supremum, infimum
  , decreasing, le, lt, unknown, orderMat, collapseO
  , CutOff(..)
  , NotWorse(..)
    -- * Call matrices
  , Index
  , CallMatrix'(..), CallMatrix
  , (>*<)
  , callMatrixInvariant
    -- * Calls
  , Call'(..), Call
  , callInvariant
    -- * Call graphs
  , CallGraph(..)
  , callGraphInvariant
  , fromList
  , toList
  , empty
  , union
  , insert
  , complete, completionInit, completionStep
  , prettyBehaviour
    -- * Tests
  , Agda.Termination.CallGraph.tests
  ) where

import Data.Array (elems)
import Data.Function
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.List hiding (union, insert)
import Data.Monoid

import Data.Foldable (Foldable)
import qualified Data.Foldable as Fold
import Data.Traversable (Traversable)
import qualified Data.Traversable as Trav

import Agda.Termination.SparseMatrix as Matrix hiding (tests)
import Agda.Termination.Semiring (HasZero(..), Semiring)
import qualified Agda.Termination.Semiring as Semiring

import Agda.Utils.Favorites (Favorites(..))
import qualified Agda.Utils.Favorites as Fav
import Agda.Utils.Function
import Agda.Utils.List hiding (tests)
import Agda.Utils.Map
import Agda.Utils.Maybe
import Agda.Utils.PartialOrd
import Agda.Utils.Pretty hiding (empty)
import Agda.Utils.QuickCheck
import Agda.Utils.TestHelpers

#include "../undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Structural orderings

-- | In the paper referred to above, there is an order R with
-- @'Unknown' '<=' 'Le' '<=' 'Lt'@.
--
-- This is generalized to @'Unknown' '<=' 'Decr k'@ where
-- @Decr 1@ replaces @Lt@ and @Decr 0@ replaces @Le@.
-- A negative decrease means an increase.  The generalization
-- allows the termination checker to record an increase by 1 which
-- can be compensated by a following decrease by 2 which results in
-- an overall decrease.
--
-- However, the termination checker of the paper itself terminates because
-- there are only finitely many different call-matrices.  To maintain
-- termination of the terminator we set a @cutoff@ point which determines
-- how high the termination checker can count.  This value should be
-- set by a global or file-wise option.
--
-- See 'Call' for more information.
--
-- TODO: document orders which are call-matrices themselves.
data Order
  = Decr Int | Unknown | Mat (Matrix Integer Order)
  deriving (Eq,Ord)

instance Show Order where
  show (Decr k) = show (- k)
  show Unknown  = "."
  show (Mat m)  = "Mat " ++ show m

instance HasZero Order where
  zeroElement = Unknown

-- | Information order: 'Unknown' is least information.
--   The more we decrease, the more information we have.
--
--   When having comparable call-matrices, we keep the lesser one.
--   Call graph completion works toward losing the good calls,
--   tending towards Unknown (the least information).
instance PartialOrd Order where
  comparable o o' = case (o, o') of
    (Unknown, Unknown) -> POEQ
    (Unknown, _      ) -> POLT
    (_      , Unknown) -> POGT
    (Decr k , Decr l ) -> comparableOrd k l
    -- Matrix-shaped orders are no longer supported
    (Mat{}  , _      ) -> __IMPOSSIBLE__
    (_      , Mat{}  ) -> __IMPOSSIBLE__

-- | Pointwise comparison.
--   Only matrices with the same dimension are comparable.
instance (Ord i, PartialOrd a) => PartialOrd (Matrix i a) where
  comparable m n
    | size m /= size n = POAny
    | otherwise        = Fold.fold $
                           zipMatrices onlym onlyn both trivial m n
    where
      -- If an element is only in @m@, then its 'Unknown' in @n@
      -- so it gotten better at best, in any case, not worse.
      onlym o = POGT
      -- If an element is only in @n@, then its 'Unknown' in @m@
      -- so we have strictly less information.
      onlyn o = POLT
      both    = comparable
      -- The zero element of the result sparse matrix is the
      -- neutral element of the monoid.
      trivial = (==mempty)

-- | A partial order, aimed at deciding whether a call graph gets
--   worse during the completion.
--
class NotWorse a where
  notWorse :: a -> a -> Bool

-- | It does not get worse then ``increase''.
--   If we are still decreasing, it can get worse: less decreasing.
instance NotWorse Order where
  o       `notWorse` Unknown = True            -- we are unboundedly increasing
  Unknown `notWorse` Decr k = k < 0            -- we are increasing
  Decr l  `notWorse` Decr k = k < 0 || l >= k  -- we are increasing or
                                               -- we are decreasing, but more
  -- Matrix-shaped orders are no longer supported
  Mat m   `notWorse` o       = __IMPOSSIBLE__
  o       `notWorse` Mat m   = __IMPOSSIBLE__
{-
  Mat m   `notWorse` Mat n   = m `notWorse` n  -- matrices are compared pointwise
  o       `notWorse` Mat n   = o `notWorse` collapse n  -- or collapsed (sound?)
  Mat m   `notWorse` o       = collapse m `notWorse` o
-}

-- | We assume the matrices have the same dimension.
instance (Ord i) => NotWorse (Matrix i Order) where
  m `notWorse` n
    | size m /= size n = __IMPOSSIBLE__
    | otherwise        = Fold.all isTrue $
                           zipMatrices onlym onlyn both trivial m n
    where
      -- If an element is only in @m@, then its 'Unknown' in @n@
      -- so it gotten better at best, in any case, not worse.
      onlym o = True     -- @== o `notWorse` Unknown@
      onlyn o = Unknown `notWorse` o
      both    = notWorse
      isTrue  = id
      trivial = id

-- | Cut off structural order comparison at some depth in termination checker?
data CutOff
  = CutOff Int
  | DontCutOff
  deriving (Eq, Ord)

instance Show CutOff where
  show (CutOff k) = show k
  show DontCutOff = "∞"

-- | Raw increase which does not cut off.
increase :: Int -> Order -> Order
increase i o = case o of
  Unknown -> Unknown
  Decr k  -> Decr $ k - i
  Mat m   -> Mat $ fmap (increase i) m

-- | Raw decrease which does not cut off.
decrease :: Int -> Order -> Order
decrease i o = increase (-i) o

-- | Smart constructor for @Decr k :: Order@ which cuts off too big values.
--
-- Possible values for @k@: @- ?cutoff '<=' k '<=' ?cutoff + 1@.
--
decr :: (?cutoff :: CutOff) => Int -> Order
decr k = case ?cutoff of
  CutOff c | k < -c -> Unknown
           | k > c  -> Decr $ c + 1
  _                 -> Decr k

-- | Smart constructor for matrix shaped orders, avoiding empty and singleton matrices.
orderMat :: Matrix Integer Order -> Order
orderMat m | Matrix.isEmpty m  = Decr 0                -- 0x0 Matrix = neutral element
           | otherwise         = case isSingleton m of
                                   Just o -> o         -- 1x1 Matrix
                                   Nothing -> Mat m    -- nxn Matrix

withinCutOff :: (?cutoff :: CutOff) => Int -> Bool
withinCutOff k = case ?cutoff of
  DontCutOff -> True
  CutOff c   -> k >= -c && k <= c + 1

isOrder :: (?cutoff :: CutOff) => Order -> Bool
isOrder (Decr k) = withinCutOff k
isOrder Unknown = True
isOrder (Mat m) = False  -- TODO: extend to matrices

prop_decr :: (?cutoff :: CutOff) => Int -> Bool
prop_decr = isOrder . decr

-- | @le@, @lt@, @decreasing@, @unknown@: for backwards compatibility, and for external use.
le :: Order
le = Decr 0

lt :: Order
lt = Decr 1

unknown :: Order
unknown = Unknown

decreasing :: Order -> Bool
decreasing (Decr k) | k > 0 = True
decreasing _ = False

instance Pretty Order where
  pretty (Decr 0) = text "="
  pretty (Decr k) = text $ show (0 - k)
  pretty Unknown  = text "?"
  pretty (Mat m)  = text "Mat" <+> pretty m

--instance Ord Order where
--    max = maxO

{- instances cannot have implicit arguments?! GHC manual says:

7.8.3.1. Implicit-parameter type constraints

You can't have an implicit parameter in the context of a class or instance declaration. For example, both these declarations are illegal:

  class (?x::Int) => C a where ...
  instance (?x::a) => Foo [a] where ...

Reason: exactly which implicit parameter you pick up depends on
exactly where you invoke a function. But the ``invocation'' of
instance declarations is done behind the scenes by the compiler, so
it's hard to figure out exactly where it is done. Easiest thing is to
outlaw the offending types.

instance (?cutoff :: CutOff) => Arbitrary Order where
  arbitrary = frequency
    [(20, return Unknown)
    ,(80, elements [- ?cutoff .. ?cutoff + 1] >>= Decr)
    ] -- no embedded matrices generated for now.
-}
instance Arbitrary Order where
  arbitrary = frequency
    [(30, return Unknown)
    ,(70, elements [0,1] >>= return . Decr)
    ] -- no embedded matrices generated for now.

instance CoArbitrary Order where
  coarbitrary (Decr k) = variant 0
  coarbitrary Unknown  = variant 1
  coarbitrary (Mat m)  = variant 2

-- | Multiplication of 'Order's. (Corresponds to sequential
-- composition.)

-- I think this funny pattern matching is because overlapping patterns
-- are producing a warning and thus an error (strict compilation settings)
(.*.) :: (?cutoff :: CutOff) => Order -> Order -> Order
Unknown  .*. _         = Unknown
(Mat m)  .*. Unknown   = Unknown
(Decr k) .*. Unknown   = Unknown
(Decr k) .*. (Decr l)  = decr (k + l)
(Decr 0) .*. (Mat m)   = Mat m
(Decr k) .*. (Mat m)   = (Decr k) .*. (collapse m)
(Mat m1) .*. (Mat m2) = if (okM m1 m2) then
                            Mat $ mul orderSemiring m1 m2
                        else
                            (collapse m1) .*. (collapse m2)
(Mat m) .*. (Decr 0)  = Mat m
(Mat m) .*. (Decr k)  = (collapse m) .*. (Decr k)

{- collapse m

We assume that m codes a permutation:  each row has at most one column
that is not Un.

To collapse a matrix into a single value, we take the best value of
each column and multiply them.  That means if one column is all Un,
i.e., no argument relates to that parameter, than the collapsed value
is also Un.

This makes order multiplication associative.

-}
collapse :: (?cutoff :: CutOff) => Matrix Integer Order -> Order
collapse m = -- if not $ Matrix.matrixInvariant m then __IMPOSSIBLE__ else
  case toLists $ Matrix.transpose m of
   [] -> __IMPOSSIBLE__   -- This can never happen if order matrices are generated by the smart constructor
   m' -> foldl1 (.*.) $ map (foldl1 maxO) m'

{- OLD CODE, does not give associative matrix multiplication:
collapse :: (?cutoff :: CutOff) => Matrix Integer Order -> Order
collapse m = foldl (.*.) le (Data.Array.elems $ diagonal m)
-}

collapseO :: (?cutoff :: CutOff) => Order -> Order
collapseO (Mat m) = collapse m
collapseO o       = o

okM :: Matrix Integer Order -> Matrix Integer Order -> Bool
okM m1 m2 = (rows $ size m2) == (cols $ size m1)

-- | The supremum of a (possibly empty) list of 'Order's.
--   More information (i.e., more decrease) is bigger.
--   'Unknown' is no information, thus, smallest.
supremum :: (?cutoff :: CutOff) => [Order] -> Order
supremum = foldr maxO Unknown

-- | @('Order', 'maxO', '.*.')@ forms a semiring, with 'Unknown' as
-- zero and 'Le' as one.

maxO :: (?cutoff :: CutOff) => Order -> Order -> Order
maxO o1 o2 = case (o1,o2) of
               (Decr k, Decr l) -> Decr (max k l) -- cut off not needed
               (Unknown,_) -> o2
               (_,Unknown) -> o1
               (Mat m1, Mat m2) -> Mat (Matrix.add maxO m1 m2)
               (Mat m,_) -> maxO (collapse m) o2
               (_,Mat m) ->  maxO o1 (collapse m)

-- | The infimum of a (non empty) list of 'Order's.
--  'Unknown' is the least element, thus, dominant.
infimum :: (?cutoff :: CutOff) => [Order] -> Order
infimum (o:l) = foldl' minO o l
infimum []    = __IMPOSSIBLE__

minO :: (?cutoff :: CutOff) => Order -> Order -> Order
minO o1 o2 = case (o1,o2) of
               (Unknown,_) -> Unknown
               (_,Unknown) -> Unknown
               (Decr k, Decr l) -> decr (min k l)
               (Mat m1, Mat m2) -> if (size m1 == size m2) then
                                       Mat $ Matrix.intersectWith minO m1 m2
                                   else
                                       minO (collapse m1) (collapse m2)
               (Mat m1,_) -> minO (collapse m1) o2
               (_,Mat m2) -> minO o1 (collapse m2)


{- Cannot have implicit arguments in instances.  Too bad!

instance Monoid Order where
  mempty = Unknown
  mappend = maxO

instance (cutoff :: Int) => SemiRing Order where
  multiply = (.*.)
-}

orderSemiring :: (?cutoff :: CutOff) => Semiring Order
orderSemiring =
  Semiring.Semiring { Semiring.add = maxO
                    , Semiring.mul = (.*.)
                    , Semiring.zero = Unknown
--                    , Semiring.one = Le
                    }

prop_orderSemiring :: (?cutoff :: CutOff) => Order -> Order -> Order -> Bool
prop_orderSemiring = Semiring.semiringInvariant orderSemiring

------------------------------------------------------------------------
-- Call matrices

-- | Call matrix indices.

type Index = Integer

-- | Call matrices. Note the call matrix invariant
-- ('callMatrixInvariant').

newtype CallMatrix' a = CallMatrix { mat :: Matrix Index a }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, CoArbitrary, PartialOrd)

type CallMatrix = CallMatrix' Order

deriving instance NotWorse CallMatrix

instance Arbitrary CallMatrix where
  arbitrary = do
    sz <- arbitrary
    callMatrix sz

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
-- Precondition: see 'Matrix.mul'.

(<*>) :: (?cutoff :: CutOff) => CallMatrix -> CallMatrix -> CallMatrix
cm1 <*> cm2 =
  CallMatrix { mat = mul orderSemiring (mat cm1) (mat cm2) }

prop_cmMul sz =
  forAll natural $ \c2 ->
  forAll (callMatrix sz) $ \cm1 ->
  forAll (callMatrix $ Size { rows = cols sz, cols = c2 }) $ \cm2 ->
    callMatrixInvariant (cm1 <*> cm2)

{- UNUSED, BUT DON'T REMOVE!
-- | Call matrix addition = minimum = pick worst information.
addCallMatrices :: (?cutoff :: CutOff) => CallMatrix -> CallMatrix -> CallMatrix
addCallMatrices cm1 cm2 = CallMatrix $
  add (Semiring.add orderSemiring) (mat cm1) (mat cm2)
-}

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

data Call' a =
  Call { source :: Index        -- ^ The function making the call.
       , target :: Index        -- ^ The function being called.
       , cm :: CallMatrix' a    -- ^ The call matrix describing the call.
       }
  deriving (Eq, Ord, Show, Functor)

type Call = Call' Order

instance PartialOrd a => PartialOrd (Call' a) where
  comparable (Call s t m) (Call s' t' m')
    | s /= s'   = POAny
    | t /= t'   = POAny
    | otherwise = comparable m m'

instance NotWorse Call where
  c1 `notWorse` c2
    | source c1 /= source c2 = __IMPOSSIBLE__
    | target c1 /= target c2 = __IMPOSSIBLE__
    | otherwise              = cm c1 `notWorse` cm c2

instance Arbitrary Call where
  arbitrary = do
    [s, t]    <- vectorOf 2 arbitrary
    cm        <- arbitrary
    return (Call { source = s, target = t, cm = cm })

instance CoArbitrary Call where
  coarbitrary (Call s t cm) =
    coarbitrary s . coarbitrary t . coarbitrary cm

prop_Arbitrary_Call :: Call -> Bool
prop_Arbitrary_Call = callInvariant

-- | 'Call' invariant.

callInvariant :: Call -> Bool
callInvariant = callMatrixInvariant . cm

-- | 'Call' combination.
--
-- Precondition: see '<*>'; furthermore the 'source' of the first
-- argument should be equal to the 'target' of the second one.

(>*<) :: (?cutoff :: CutOff) => Call -> Call -> Call
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

newtype CallGraph meta = CallGraph { theCallGraph :: Map Call meta }
  deriving (Eq, Show)

-- | 'CallGraph' invariant.

callGraphInvariant :: CallGraph meta -> Bool
callGraphInvariant = all (callInvariant . fst) . toList

-- | Converts a call graph to a list of calls with associated meta
-- information.

toList :: CallGraph meta -> [(Call, meta)]
toList = Map.toList . theCallGraph

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
union cs1 cs2 = CallGraph $ (Map.unionWith mappend `on` theCallGraph) cs1 cs2

-- | 'CallGraph' is a monoid under 'union'.

instance Monoid meta => Monoid (CallGraph meta) where
  mempty  = empty
  mappend = union

-- | Inserts a call into a call graph.

insert :: Monoid meta
       => Call -> meta -> CallGraph meta -> CallGraph meta
insert c m = CallGraph . Map.insertWith mappend c m . theCallGraph

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

-- | Call graph representation as map from source-target node pair to edge

data SourceTarget = SourceTarget { src :: Index, tgt :: Index }
  deriving (Eq, Ord, Show)

type CMSet       = Favorites CallMatrix
type CallGraphST = Map SourceTarget CMSet

-- | A set of favorites @s@ is not worse than a set of favorites @t@
--   if for each @a `elem` s@ there a @b `elem` t@
--   such that @a@ is not worse than @b@.

instance NotWorse a => NotWorse (Favorites a) where
  Favorites s `notWorse` Favorites t =
    (`all` t) $ \ a ->
    (`any` s) $ \ b -> a `notWorse` b


-- | A call graph has not become worse
--   if it does not connect previously unconnected nodes
--   and each edge has not gotten worse.

instance NotWorse CallGraphST where
  g1 `notWorse` g2 = (`allWithKey` g1) $ \ k cms1 ->
    -- We can ignore edges that are only g2 (impossible anyway).
    -- If the edge is only present in g1, we've gotten worse.
    caseMaybe (Map.lookup k g2) False $ \ cms2 ->
      -- If the edge is present in both, we compare.
      cms1 `notWorse` cms2

{-
instance NotWorse CallGraphST where
  g1 `notWorse` g2 = allWithKey edgeNotWorse g1
    -- we can ignore edges that are only g2 (impossible anyway)
    where
      edgeNotWorse :: SourceTarget -> CMSet -> Bool
      edgeNotWorse k cms1 =
        caseMaybe (Map.lookup k g2)
          -- if the edge is only present in g1, we've gotten worse
          False $
          -- if the edge is present in both, we compare
          (\ cms2 -> cms1 `notWorse` cms2)
{- TRASH:
          \ l2 -> flip all cms1 $ \ cm1 -> any (cm1 `notWorse`) (favorites l2)
          case Fav.compareWithFavorites cm1 l2 of
            Fav.IsDominated{}       -> True  -- no new info, it's not gotten worse
            Fav.Dominates cms2 _rest -> all (cm1 `notWorse`) cms2
-}
-}

-- | Convert a call graph such that all calls between nodes are grouped together.
--
--   TODO: store the call graph in this form from the beginning.

toCallGraphST :: CallGraph meta -> CallGraphST
toCallGraphST =
    Map.fromListWith Fav.union . map fromCall . Map.keys . theCallGraph
  where fromCall (Call s t m) = (SourceTarget s t, Fav.singleton m)

instance NotWorse (CallGraph meta) where
  g1 `notWorse` g2 = toCallGraphST g1 `notWorse` toCallGraphST g2


-- | Call graph combination. (Application of '>*<' to all pairs @(c1,
-- c2)@ for which @'source' c1 = 'target' c2@.)
--
-- Precondition: see '<*>'.

combine
  :: (Monoid meta, ?cutoff :: CutOff) => CallGraph meta -> CallGraph meta -> CallGraph meta
combine s1 s2 = fromList $
  [ (c1 >*< c2, m1 `mappend` m2)
  | (c1, m1) <- toList s1, (c2, m2) <- toList s2
  , source c1 == target c2
  ]

-- | Call graph comparison.
--   A graph @cs'@ is ``worse'' than @cs@ if it has a new edge (call)
--   or a call got worse, which means that one of its elements
--   that was better or equal to 'Le' moved a step towards 'Un'.
--
--   A call graph is complete if combining it with itself does not make it
--   any worse.  This is sound because of monotonicity:  By combining a graph
--   with itself, it can only get worse, but if it does not get worse after
--   one such step, it gets never any worse.

-- | @'complete' cs@ completes the call graph @cs@. A call graph is
-- complete if it contains all indirect calls; if @f -> g@ and @g ->
-- h@ are present in the graph, then @f -> h@ should also be present.

complete :: (?cutoff :: CutOff) => Monoid meta => CallGraph meta -> CallGraph meta
complete cs = iterateUntil notWorse (completionStep cs0) cs0
  where cs0 = completionInit cs

{-
complete cs = complete' safeCS
  where
  safeCS = ensureCompletePrecondition cs

  complete' cs | cs' .==. cs = cs
               | otherwise   = complete' cs'
    where
    cs' = cs `union` combine cs safeCS
    (.==.) = ((==) `on` (Map.keys . theCallGraph))
-}

completionStep :: (?cutoff :: CutOff) => Monoid meta =>
  CallGraph meta -> CallGraph meta -> CallGraph meta
completionStep gOrig gThis = gThis `union` (gThis `combine` gOrig)

prop_complete :: (?cutoff :: CutOff) => Property
prop_complete =
  forAll (callGraph :: Gen (CallGraph [Integer])) $ \cs ->
    isComplete (complete cs)

-- | Returns 'True' iff the call graph is complete.

isComplete :: (Ord meta, Monoid meta, ?cutoff :: CutOff) => CallGraph meta -> Bool
isComplete s = (s `union` (s `combine` s)) `notWorse` s
{-
isComplete s = all (`Map.member` theCallGraph s) combinations
  where
  calls = toList s
  combinations =
    [ c2 >*< c1 | (c1, _) <- calls, (c2, _) <- calls
                , target c1 == source c2 ]
-}

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
--   all calls between two functions have the same call matrix dimensions.
--   The result satisfies 'completePrecondition'.

completionInit
  :: Monoid meta => CallGraph meta -> CallGraph meta
completionInit cs =
  CallGraph $ Map.mapKeysWith mappend pad $ theCallGraph cs
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
    let cs' = completionInit cs in
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

{- RETIRED CODE
showBehaviour :: Show meta => CallGraph meta -> String
showBehaviour = concatMap showCall . toList
  where
  showCall (c, meta) | source c /= target c = ""
                     | otherwise            = unlines
    [ "Function:  " ++ show (source c)
    , "Behaviour: " ++ show (elems $ diagonal $ mat $ cm c)
    , "Meta info: " ++ show meta
    ]
-}

instance Show meta => Pretty (CallGraph meta) where
  pretty = vcat . map prettyCall . toList
    where
    prettyCall (c, meta) = align 20
      [ ("Source:",    text $ show $ source c)
      , ("Target:",    text $ show $ target c)
      , ("Matrix:",    pretty (mat $ cm c))
      -- , ("Meta info:", text $ show meta) -- not pretty at all
      ]

-- | Displays the recursion behaviour corresponding to a call graph.

prettyBehaviour :: Show meta => CallGraph meta -> Doc
prettyBehaviour = vcat . map prettyCall . filter (toSelf . fst) . toList
  where
  toSelf c = source c == target c

  prettyCall (c, meta) = vcat $ map text
    [ "Function:  " ++ show (source c)
    , "Behaviour: " ++ show (elems $ diagonal $ mat $ cm c)
    , "Meta info: " ++ show meta
    ]

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.CallGraph"
  [ quickCheck' callMatrixInvariant
  , quickCheck' prop_decr
  , quickCheck' prop_orderSemiring
  , quickCheck' prop_Arbitrary_CallMatrix
  , quickCheck' prop_callMatrix
  , quickCheck' prop_cmMul
  , quickCheck' prop_Arbitrary_Call
  , quickCheck' prop_callGraph
  , quickCheck' prop_complete
  , quickCheck' prop_ensureCompletePrecondition
  ]
  where ?cutoff = DontCutOff -- CutOff 2  -- don't cut off in tests!
