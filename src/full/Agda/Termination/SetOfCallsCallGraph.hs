-- {-# LANGUAGE CPP #-}
-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- {-# LANGUAGE ImplicitParams #-}

-- -- | Call graphs and related concepts, more or less as defined in
-- --     \"A Predicative Analysis of Structural Recursion\" by
-- --     Andreas Abel and Thorsten Altenkirch.

-- -- Originally copied from Agda1 sources.

-- module Agda.Termination.CallGraph
--   ( -- * Calls
--     Index
--   , Call', Call, mkCall, source, target, cm
--   , (>*<)
--     -- * Call graphs
--   , CallGraph(..)
--   , fromList
--   , toList
--   , empty
--   , union
--   , insert
--   , complete, completionInit, completionStep
--   , prettyBehaviour
--     -- * Tests
--   , Agda.Termination.CallGraph.tests
--   ) where

-- import Prelude hiding (null)

-- import Data.Function
-- import Data.Map (Map, (!))
-- import qualified Data.Map as Map
-- import Data.List hiding (union, insert, null)
-- import Data.Monoid

-- import Data.Foldable (Foldable)
-- import qualified Data.Foldable as Fold
-- import Data.Traversable (Traversable)
-- import qualified Data.Traversable as Trav

-- import Agda.Termination.CallMatrix hiding (tests)
-- import Agda.Termination.CutOff
-- import Agda.Termination.Order
-- import Agda.Termination.SparseMatrix as Matrix hiding (tests)
-- import Agda.Termination.Semiring (HasZero(..), Semiring)
-- import qualified Agda.Termination.Semiring as Semiring

-- import Agda.Utils.Favorites (Favorites(Favorites))
-- import qualified Agda.Utils.Favorites as Fav
-- import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Edge(..),Graph(..))
-- import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph

-- import Agda.Utils.Function
-- import Agda.Utils.List hiding (tests)
-- import Agda.Utils.Map
-- import Agda.Utils.Maybe
-- import Agda.Utils.Monad
-- import Agda.Utils.Null
-- import Agda.Utils.PartialOrd
-- import Agda.Utils.Pretty
-- import Agda.Utils.QuickCheck hiding (label)
-- import Agda.Utils.TestHelpers

-- #include "undefined.h"
-- import Agda.Utils.Impossible

-- ------------------------------------------------------------------------
-- -- Calls

-- -- | Call graph nodes.
-- --
-- --   Machine integer 'Int' is sufficient, since we cannot index more than
-- --   we have addresses on our machine.

-- type Index = Int

-- -- | This datatype encodes information about a single recursive
-- -- function application. The columns of the call matrix stand for
-- -- 'source' function arguments (patterns); the first argument has
-- -- index 0, the second 1, and so on. The rows of the matrix stand for
-- -- 'target' function arguments. Element @(i, j)@ in the matrix should
-- -- be computed as follows:
-- --
-- --   * 'Lt' (less than) if the @j@-th argument to the 'target'
-- --     function is structurally strictly smaller than the @i@-th
-- --     pattern.
-- --
-- --   * 'Le' (less than or equal) if the @j@-th argument to the
-- --     'target' function is structurally smaller than the @i@-th
-- --     pattern.
-- --
-- --   * 'Unknown' otherwise.
-- --
-- --   The structural ordering used is defined in the paper referred to
-- --   above.

-- type Call' a = Edge Index Index (CallMatrix' a)
-- mkCall = Edge
-- cm = label

-- type Call = Call' Order

-- instance HasZero a => Diagonal (Call' a) a where
--   diagonal = diagonal . cm

-- instance PartialOrd a => PartialOrd (Call' a) where
--   comparable (Edge s t m) (Edge s' t' m')
--     | s /= s'   = POAny
--     | t /= t'   = POAny
--     | otherwise = comparable m m'

-- instance NotWorse Call where
--   c1 `notWorse` c2
--     | source c1 /= source c2 = __IMPOSSIBLE__
--     | target c1 /= target c2 = __IMPOSSIBLE__
--     | otherwise              = cm c1 `notWorse` cm c2

-- -- | 'Call' combination.
-- --
-- --   @f --(c2)--> g --(c1)--> h@  is combined to @f --(c1 >*< c2)--> h@
-- --
-- --   Note the reversed order of multiplication:
-- --   The matrix @c1@ of the second call @g-->h@ in the sequence
-- --   @f-->g-->h@ is multiplied with the matrix @c2@ of the first call.
-- --
-- --   Preconditions:
-- --   @source c1 == target c2@
-- --   @c1@ has dimensions @ar(h) × ar(g)@.
-- --   @c2@ has dimensions @ar(g) × ar(f)@.
-- --
-- --   Postcondition:
-- --   @c1 >*< c2@ has dimensions @ar(h) × ar(f)@.

-- instance CallComb Call where
--   c1 >*< c2 | g == g' = Edge f h (cm c1 >*< cm c2)
--     where f  = source c2
--           g  = target c2
--           g' = source c1
--           h  = target c1
--   c1 >*< c2 = __IMPOSSIBLE__

-- ------------------------------------------------------------------------
-- -- Call graphs

-- -- | A call graph is a set of calls. Every call also has some
-- -- associated meta information, which should be 'Monoid'al so that the
-- -- meta information for different calls can be combined when the calls
-- -- are combined.

-- newtype CallGraph cinfo = CallGraph { theCallGraph :: Map Call cinfo }
--   deriving (Eq, Show)

-- -- | Converts a call graph to a list of calls with associated meta
-- -- information.

-- toList :: CallGraph cinfo -> [(Call, cinfo)]
-- toList = Map.toList . theCallGraph

-- -- | Converts a list of calls with associated meta information to a
-- -- call graph.

-- fromList :: Monoid cinfo => [(Call, cinfo)] -> CallGraph cinfo
-- fromList = CallGraph . Map.fromListWith mappend

-- -- | Creates an empty call graph.

-- empty :: CallGraph cinfo
-- empty = CallGraph Map.empty

-- -- | Takes the union of two call graphs.

-- union :: Monoid cinfo
--       => CallGraph cinfo -> CallGraph cinfo -> CallGraph cinfo
-- union cs1 cs2 = CallGraph $ (Map.unionWith mappend `on` theCallGraph) cs1 cs2

-- -- | 'CallGraph' is a monoid under 'union'.

-- instance Monoid cinfo => Monoid (CallGraph cinfo) where
--   mempty  = empty
--   mappend = union

-- -- | Inserts a call into a call graph.

-- insert :: Monoid cinfo
--        => Index -> Index -> CallMatrix -> cinfo
--        -> CallGraph cinfo -> CallGraph cinfo
-- insert s t cm m = CallGraph . Map.insertWith mappend (Edge s t cm) m . theCallGraph

-- -- | Generates a call graph.

-- callGraph :: (Monoid cinfo, Arbitrary cinfo) => Gen (CallGraph cinfo)
-- callGraph = do
--   indices <- fmap nub arbitrary
--   n <- natural
--   let noMatrices | null indices = 0
--                  | otherwise    = n `min` 3  -- Not too many.
--   fmap fromList $ vectorOf noMatrices (matGen indices)
--   where
--   matGen indices = do
--     [s, t] <- vectorOf 2 (elements indices)
--     [c, r] <- vectorOf 2 (choose (0, 2))     -- Not too large.
--     m <- callMatrix (Size { rows = r, cols = c })
--     callId <- arbitrary
--     return (Edge s t m, callId)

-- -- | Call graph representation as map from source-target node pair to edge

-- data SourceTarget = SourceTarget { src :: Index, tgt :: Index }
--   deriving (Eq, Ord, Show)

-- type CMSet       = Favorites CallMatrix
-- type CallGraphST = Map SourceTarget CMSet

-- -- | A set of favorites @s@ is not worse than a set of favorites @t@
-- --   if for each @a `elem` s@ there exists some @b `elem` t@
-- --   such that @a@ is not worse than @b@.

-- instance NotWorse a => NotWorse (Favorites a) where
--   Favorites s `notWorse` Favorites t =
--     (`all` s) $ \ a ->
--     (`any` t) $ \ b -> a `notWorse` b

-- -- | A call graph has not become worse
-- --   if it does not connect previously unconnected nodes
-- --   and each edge has not gotten worse.

-- instance NotWorse CallGraphST where
--   g1 `notWorse` g2 = (`allWithKey` g1) $ \ k cms1 ->
--     -- We can ignore edges that are only g2 (impossible anyway).
--     -- If the edge is only present in g1, we've gotten worse.
--     caseMaybe (Map.lookup k g2) False $ \ cms2 ->
--       -- If the edge is present in both, we compare.
--       cms1 `notWorse` cms2

-- {-
-- instance NotWorse CallGraphST where
--   g1 `notWorse` g2 = allWithKey edgeNotWorse g1
--     -- we can ignore edges that are only g2 (impossible anyway)
--     where
--       edgeNotWorse :: SourceTarget -> CMSet -> Bool
--       edgeNotWorse k cms1 =
--         caseMaybe (Map.lookup k g2)
--           -- if the edge is only present in g1, we've gotten worse
--           False $
--           -- if the edge is present in both, we compare
--           (\ cms2 -> cms1 `notWorse` cms2)
-- {- TRASH:
--           \ l2 -> flip all cms1 $ \ cm1 -> any (cm1 `notWorse`) (favorites l2)
--           case Fav.compareWithFavorites cm1 l2 of
--             Fav.IsDominated{}       -> True  -- no new info, it's not gotten worse
--             Fav.Dominates cms2 _rest -> all (cm1 `notWorse`) cms2
-- -}
-- -}

-- -- | Convert a call graph such that all calls between nodes are grouped together.
-- --
-- --   TODO: store the call graph in this form from the beginning.

-- toCallGraphST :: CallGraph cinfo -> CallGraphST
-- toCallGraphST =
--     Map.fromListWith Fav.union . map fromCall . Map.keys . theCallGraph
--   where fromCall (Edge s t m) = (SourceTarget s t, Fav.singleton m)

-- instance NotWorse (CallGraph cinfo) where
--   g1 `notWorse` g2 = toCallGraphST g1 `notWorse` toCallGraphST g2


-- -- | Call graph combination.
-- --
-- --   Application of '>*<' to all pairs @(c1,c2)@
-- --   for which @'source' c1 = 'target' c2@.)

-- combine
--   :: (Monoid cinfo, ?cutoff :: CutOff) => CallGraph cinfo -> CallGraph cinfo -> CallGraph cinfo
-- combine s1 s2 = fromList $
--   [ (c1 >*< c2, m1 `mappend` m2)
--   | (c1, m1) <- toList s1, (c2, m2) <- toList s2
--   , source c1 == target c2
--   ]

-- -- | Call graph comparison.
-- --   A graph @cs'@ is ``worse'' than @cs@ if it has a new edge (call)
-- --   or a call got worse, which means that one of its elements
-- --   that was better or equal to 'Le' moved a step towards 'Un'.
-- --
-- --   A call graph is complete if combining it with itself does not make it
-- --   any worse.  This is sound because of monotonicity:  By combining a graph
-- --   with itself, it can only get worse, but if it does not get worse after
-- --   one such step, it gets never any worse.

-- -- | @'complete' cs@ completes the call graph @cs@. A call graph is
-- -- complete if it contains all indirect calls; if @f -> g@ and @g ->
-- -- h@ are present in the graph, then @f -> h@ should also be present.

-- complete :: (?cutoff :: CutOff) => Monoid cinfo => CallGraph cinfo -> CallGraph cinfo
-- complete cs = iterateUntil notWorse (completionStep cs0) cs0
--   where cs0 = completionInit cs

-- {-
-- complete cs = complete' safeCS
--   where
--   safeCS = ensureCompletePrecondition cs

--   complete' cs | cs' .==. cs = cs
--                | otherwise   = complete' cs'
--     where
--     cs' = cs `union` combine cs safeCS
--     (.==.) = ((==) `on` (Map.keys . theCallGraph))
-- -}

-- completionStep :: (?cutoff :: CutOff) => Monoid cinfo =>
--   CallGraph cinfo -> CallGraph cinfo -> CallGraph cinfo
-- completionStep gOrig gThis = gThis `union` (gThis `combine` gThis)
-- -- Andreas, 2014-01-09: The following does not iterate enough
-- -- to generate the necessary idempotent matrices.  (See issue 1014.)
-- -- completionStep gOrig gThis = gThis `union` (gThis `combine` gOrig)

-- prop_complete :: (?cutoff :: CutOff) => Property
-- prop_complete =
--   forAll (callGraph :: Gen (CallGraph [Integer])) $ \cs ->
--     isComplete (complete cs)

-- -- | Returns 'True' iff the call graph is complete.

-- isComplete :: (Ord cinfo, Monoid cinfo, ?cutoff :: CutOff) => CallGraph cinfo -> Bool
-- isComplete s = (s `union` (s `combine` s)) `notWorse` s
-- {-
-- isComplete s = all (`Map.member` theCallGraph s) combinations
--   where
--   calls = toList s
--   combinations =
--     [ c2 >*< c1 | (c1, _) <- calls, (c2, _) <- calls
--                 , target c1 == source c2 ]
-- -}

-- -- | Checks whether every 'Index' used in the call graph corresponds
-- -- to a fixed number of arguments (i.e. rows\/columns).

-- completePrecondition :: CallGraph cinfo -> Bool
-- completePrecondition cs =
--   all (allEqual . map snd) $
--   groupOn fst $
--   concat [ [(source c, cols $ size' c), (target c, rows $ size' c)]
--          | (c, _) <- toList cs]
--   where
--   size' = size . mat . cm

-- -- | Returns a call graph padded with 'unknown's in such a way that
-- --   all calls between two functions have the same call matrix dimensions.
-- --   The result satisfies 'completePrecondition'.

-- completionInit
--   :: Monoid cinfo => CallGraph cinfo -> CallGraph cinfo
-- completionInit cs =
--   CallGraph $ Map.mapKeysWith mappend pad $ theCallGraph cs
--   where
--   -- The maximum number of arguments detected for every index.
--   nArgs :: Map Index Int
--   nArgs = foldr (\c m -> insert (source c) (cols' c) $
--                           insert (target c) (rows' c) m)
--                  Map.empty
--                  (map fst $ toList cs)
--     where insert = Map.insertWith max

--   pad c = c { label = CallMatrix { mat = padRows $ padCols $ mat $ cm c } }
--     where
--     padCols = iterate' ((nArgs ! source c) - cols' c)
--                        (addColumn unknown)

--     padRows = iterate' ((nArgs ! target c) - rows' c)
--                        (addRow unknown)

--   cols'  = cols . size'
--   rows'  = rows . size'
--   size'  = size . mat . cm

-- prop_ensureCompletePrecondition =
--   forAll (callGraph :: Gen (CallGraph [Integer])) $ \cs ->
--     let cs' = completionInit cs in
--     completePrecondition cs'
--     -- &&
--     -- all callInvariant (map fst $ toList cs')
--     &&
--     and [ or [ new .==. old | (old, _) <- toList cs ]
--         | (new, _) <- toList cs' ]
--   where
--   c1 .==. c2 = all (all (uncurry (==)))
--                    ((zipZip `on` (toLists . mat . cm)) c1 c2)

--   -- zipZip discards the new elements.
--   zipZip :: [[a]] -> [[b]] -> [[(a, b)]]
--   zipZip xs ys = map (uncurry zip) $ zip xs ys

-- -- | Displays the recursion behaviour corresponding to a call graph.

-- {- RETIRED CODE
-- showBehaviour :: Show cinfo => CallGraph cinfo -> String
-- showBehaviour = concatMap showCall . toList
--   where
--   showCall (c, cinfo) | source c /= target c = ""
--                      | otherwise            = unlines
--     [ "Function:  " ++ show (source c)
--     , "Behaviour: " ++ show (elems $ diagonal $ mat $ cm c)
--     , "Meta info: " ++ show cinfo
--     ]
-- -}

-- instance Show cinfo => Pretty (CallGraph cinfo) where
--   pretty = vcat . map prettyCall . toList
--     where
--     prettyCall (c, cinfo) = align 20
--       [ ("Source:",    text $ show $ source c)
--       , ("Target:",    text $ show $ target c)
--       , ("Matrix:",    pretty (mat $ cm c))
--       -- , ("Meta info:", text $ show cinfo) -- not pretty at all
--       ]

-- -- | Displays the recursion behaviour corresponding to a call graph.

-- prettyBehaviour :: Show cinfo => CallGraph cinfo -> Doc
-- prettyBehaviour = vcat . map prettyCall . filter (toSelf . fst) . toList
--   where
--   toSelf c = source c == target c

--   prettyCall (c, cinfo) = vcat $ map text
--     [ "Function:  " ++ show (source c)
--     , "Behaviour: " ++ show (diagonal $ mat $ cm c)
--     , "Meta info: " ++ show cinfo
--     ]

-- ------------------------------------------------------------------------
-- -- All tests

-- tests :: IO Bool
-- tests = runTests "Agda.Termination.CallGraph"
--   [ quickCheck' prop_complete
--   , quickCheck' prop_ensureCompletePrecondition
--   ]
--   where ?cutoff = DontCutOff -- CutOff 2  -- don't cut off in tests!


-- {- RETIRED: NO invariant on calls

-- prop_Arbitrary_Call :: Call -> Bool
-- prop_Arbitrary_Call = callInvariant

-- -- | 'Call' invariant.

-- callInvariant :: Call -> Bool
-- callInvariant = callMatrixInvariant . cm

-- -- | 'CallGraph' invariant.

-- callGraphInvariant :: CallGraph cinfo -> Bool
-- callGraphInvariant = all (callInvariant . fst) . toList

-- prop_callGraph =
--   forAll (callGraph :: Gen (CallGraph [Integer])) $ \cs ->
--     callGraphInvariant cs

-- -}
