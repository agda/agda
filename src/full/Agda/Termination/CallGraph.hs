{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams             #-}

-- | Call graphs and related concepts, more or less as defined in
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch.

-- Originally copied from Agda1 sources.

module Agda.Termination.CallGraph
  ( -- * Calls
    Node
  , Call, mkCall, mkCall', source, target, callMatrixSet
  , (>*<)
    -- * Call graphs
  , CallGraph(..)
  , targetNodes
  , fromList
  , toList
  , union
  , insert
  , complete, completionStep
  -- , prettyBehaviour
  ) where

import Prelude hiding (null)

import qualified Data.List as List
import Data.Semigroup
import Data.Set (Set)

import Agda.Termination.CallMatrix (CallMatrix, CallMatrixAug(..), CMSet(..), CallComb(..))
import qualified Agda.Termination.CallMatrix as CMSet
import Agda.Termination.CutOff
import Agda.Termination.SparseMatrix as Matrix

import Agda.Utils.Favorites (Favorites)
import qualified Agda.Utils.Favorites as Fav
import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Edge(..),Graph(..))
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph

import Agda.Utils.Function
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.PartialOrd
import Agda.Utils.Pretty
import Agda.Utils.Singleton
import Agda.Utils.Tuple

------------------------------------------------------------------------
-- Calls

-- | Call graph nodes.
--
--   Machine integer 'Int' is sufficient, since we cannot index more than
--   we have addresses on our machine.

type Node = Int

-- | Calls are edges in the call graph.
--   It can be labelled with several call matrices if there
--   are several pathes from one function to another.

type Call cinfo = Edge Node (CMSet cinfo)

callMatrixSet :: Call cinfo -> CMSet cinfo
callMatrixSet = label

-- | Make a call with a single matrix.
mkCall :: Node -> Node -> CallMatrix -> cinfo -> Call cinfo
mkCall s t m cinfo = Edge s t $ singleton $ CallMatrixAug m cinfo

-- | Make a call with empty @cinfo@.
mkCall' :: Monoid cinfo => Node -> Node -> CallMatrix -> Call cinfo
mkCall' s t m = mkCall s t m mempty

------------------------------------------------------------------------
-- Call graphs

-- | A call graph is a set of calls. Every call also has some
-- associated meta information, which should be 'Monoid'al so that the
-- meta information for different calls can be combined when the calls
-- are combined.

newtype CallGraph cinfo = CallGraph { theCallGraph :: Graph Node (CMSet cinfo) }
  deriving (Show)


-- | Returns all the nodes with incoming edges.  Somewhat expensive. @O(e)@.

targetNodes :: CallGraph cinfo -> Set Node
targetNodes = Graph.targetNodes . theCallGraph

-- | Converts a call graph to a list of calls with associated meta
--   information.

toList :: CallGraph cinfo -> [Call cinfo]
toList = Graph.edges . theCallGraph

-- | Converts a list of calls with associated meta information to a
--   call graph.

fromList :: [Call cinfo] -> CallGraph cinfo
fromList = CallGraph . Graph.fromEdgesWith CMSet.union

-- | 'null' checks whether the call graph is completely disconnected.
instance Null (CallGraph cinfo) where
  empty = CallGraph Graph.empty
  null  = List.all (null . label) . toList

-- | Takes the union of two call graphs.

union :: CallGraph cinfo -> CallGraph cinfo -> CallGraph cinfo
union (CallGraph cs1) (CallGraph cs2) = CallGraph $
  Graph.unionWith CMSet.union cs1 cs2

-- | 'CallGraph' is a monoid under 'union'.

instance Semigroup (CallGraph cinfo) where
  (<>) = union

instance Monoid (CallGraph cinfo) where
  mempty  = empty
  mappend = (<>)

-- | Inserts a call into a call graph.

insert :: Node -> Node -> CallMatrix -> cinfo
       -> CallGraph cinfo -> CallGraph cinfo
insert s t cm cinfo = CallGraph . Graph.insertEdgeWith CMSet.union e . theCallGraph
  where e = mkCall s t cm cinfo


-- * Combination of a new thing with an old thing
--   returning a really new things and updated old things.

type CombineNewOldT a = a -> a -> (a, a)

class CombineNewOld a where
  combineNewOld :: CombineNewOldT a

instance PartialOrd a => CombineNewOld (Favorites a) where
  combineNewOld new old = (new', Fav.unionCompared (new', old'))
    where (new', old') = Fav.compareFavorites new old

deriving instance CombineNewOld (CMSet cinfo)

instance (Monoid a, CombineNewOld a, Ord n) => CombineNewOld (Graph n a) where
  combineNewOld new old = Graph.unzip $ Graph.unionWith comb new' old'
    where
      new' = (,mempty) <$> new
      old' = (mempty,) <$> old
      comb (new1,old1) (new2,old2)  -- TODO: ensure old1 is null
        = mapFst (new2 `mappend`) $ combineNewOld new1 old2
        -- -- | old1 == mempty = mapFst (new2 `mappend`) $ combineNewOld new1 old2
        -- -- | otherwise      = __IMPOSSIBLE__

      -- Filter unlabelled edges from the resulting new graph.
      -- filt = Graph.filterEdges (not . null)

-- | Call graph combination.
--
--   Application of '>*<' to all pairs @(c1,c2)@
--   for which @'source' c1 = 'target' c2@.)

-- GHC supports implicit-parameter constraints in instance declarations
-- only from 7.4.  To maintain compatibility with 7.2, we skip this instance:
-- KEEP:
-- instance (Monoid cinfo, ?cutoff :: CutOff) => CombineNewOld (CallGraph cinfo) where
--   combineNewOld (CallGraph new) (CallGraph old) = CallGraph -*- CallGraph $ combineNewOld comb old
--     -- combined calls:
--     where comb = Graph.composeWith (>*<) CMSet.union new old

-- Non-overloaded version:
combineNewOldCallGraph :: (Monoid cinfo, ?cutoff :: CutOff) => CombineNewOldT (CallGraph cinfo)
combineNewOldCallGraph (CallGraph new) (CallGraph old) = CallGraph -*- CallGraph $ combineNewOld comb old
    -- combined calls:
    where comb = Graph.composeWith (>*<) CMSet.union new old

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

complete :: (?cutoff :: CutOff) => Monoid cinfo => CallGraph cinfo -> CallGraph cinfo
complete cs = repeatWhile (mapFst (not . null) . completionStep cs) cs

completionStep :: (?cutoff :: CutOff) => Monoid cinfo =>
  CallGraph cinfo -> CallGraph cinfo -> (CallGraph cinfo, CallGraph cinfo)
completionStep gOrig gThis = combineNewOldCallGraph gOrig gThis

------------------------------------------------------------------------
-- * Printing
------------------------------------------------------------------------

-- | Displays the recursion behaviour corresponding to a call graph.

instance Pretty cinfo => Pretty (CallGraph cinfo) where
  pretty = vcat . map prettyCall . toList
    where
    prettyCall e = if null (callMatrixSet e) then empty else align 20 $
      [ ("Source:",    text $ show $ source e)
      , ("Target:",    text $ show $ target e)
      , ("Matrix:",    pretty $ callMatrixSet e)
      ]

-- -- | Displays the recursion behaviour corresponding to a call graph.

-- prettyBehaviour :: Show cinfo => CallGraph cinfo -> Doc
-- prettyBehaviour = vcat . map prettyCall . filter toSelf . toList
--   where
--   toSelf c = source c == target c

--   prettyCall e = vcat $ map text
--     [ "Function:  " ++ show (source e)
-- --    , "Behaviour: " ++ show (diagonal $ mat $ cm c)  -- TODO
-- --    , "Meta info: " ++ show cinfo
--     ]
