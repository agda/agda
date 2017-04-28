{-# LANGUAGE CPP                       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Agda.TypeChecking.SizedTypes.WarshallSolver where

import Prelude hiding (truncate)

import Control.Applicative hiding (Const)
import Control.Monad

import Data.Function (on)
import Data.List as List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (for)

import Agda.TypeChecking.SizedTypes.Syntax
import Agda.TypeChecking.SizedTypes.Utils

import Agda.Utils.Graph.AdjacencyMap.Unidirectional
  (Edge(..), Nodes(..), nodes, computeNodes)
-- (Edge'(..), allNodes, emptyGraph, insertEdge, graphToList, graphFromList, nodes, lookupEdge, outgoing, incoming, diagonal, transClos)
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph

#include "undefined.h"
import Agda.Utils.Impossible

type Graph r f a = Graph.Graph (Node r f) (Node r f) a
type Edge' r f a = Graph.Edge  (Node r f) (Node r f) a
type Key r f = Edge' r f ()
type Nodes r f = Graph.Nodes (Node r f)
type LabelledEdge r f = Edge' r f Label

src :: Edge s t e -> s
src = Graph.source

dest :: Edge s t e -> t
dest = Graph.target

lookupEdge :: (Ord s, Ord t) => Graph.Graph s t e -> s -> t -> Maybe e
lookupEdge g s t = Graph.lookup s t g

graphToList :: Graph.Graph s t e -> [Edge s t e]
graphToList = Graph.toList

graphFromList :: (Ord s, Ord t) => [Edge s t e] -> Graph.Graph s t e
graphFromList = Graph.fromList

insertEdge :: (Ord s, Ord t, MeetSemiLattice e, Top e) =>
              Edge s t e -> Graph.Graph s t e -> Graph.Graph s t e
insertEdge e g
  | isTop (label e) = g
  | otherwise       = Graph.insertEdgeWith meet e g

-- | Compute list of edges that start in a given node.
outgoing :: (Ord r, Ord f) => Graph r f a -> Node r f -> [Edge' r f a]
outgoing g s = Graph.edgesFrom g [s]

-- | Compute list of edges that target a given node.
--
--   Note: expensive for unidirectional graph representations.
incoming :: (Ord r, Ord f) => Graph r f a -> Node r f -> [Edge' r f a]
incoming g t = Graph.edgesTo g [t]

-- | @Set.foldl@ does not exist in legacy versions of the @containers@ package.
setFoldl :: (b -> a -> b) -> b -> Set a -> b
setFoldl step start = List.foldl' step start . Set.toAscList
-- setFoldl = Set.foldl'

-- | Floyd-Warshall algorithm.
transClos :: forall n a . (Ord n, Dioid a) => Graph.Graph n n a -> Graph.Graph n n a
transClos g = setFoldl step g $ allNodes ns
  where
    ns       = computeNodes g
    srcs     = Set.toAscList $ srcNodes  ns
    dests    = Set.toAscList $ tgtNodes ns
    -- @step g v@ adds all intermediate edges @u --> w@ via @v@ to @g@
    -- step :: (Ord n, Dioid a) => Graph.Graph n n a -> n -> Graph.Graph n n a
    step g v = foldl (flip insertEdge) g $
      [ Edge u w $ l1 `compose` l2
        | u <- srcs
        , w <- dests
        , l1 <- maybeToList $ lookupEdge g u v
        , l2 <- maybeToList $ lookupEdge g v w
      ]

-- * Edge weights

data Weight
  = Offset Offset
  | Infinity
  deriving (Eq)

instance Show Weight where
  show (Offset x) = show x
  show Infinity   = "∞"

instance Ord Weight where
  x        <= Infinity = True
  Infinity <= y        = False
  Offset x <= Offset y = x <= y

instance MeetSemiLattice Weight where
  meet = min

instance Top Weight where
  top  = Infinity

instance Enum Weight where
  succ (Offset x) = Offset (succ x)
  succ (Infinity) = Infinity
  pred (Offset x) = Offset (pred x)
  pred (Infinity) = Infinity
  toEnum = Offset . toEnum
  fromEnum (Offset x) = fromEnum x
  fromEnum (Infinity) = __IMPOSSIBLE__

-- | Partial implementation of @Num@.
instance Num Weight where
  Infinity + y        = Infinity
  x + Infinity        = Infinity
  Offset x + Offset y = Offset $ x + y
  Infinity - Offset y = Infinity
  Offset x - Offset y = Offset $ x - y
  x        - Infinity = __IMPOSSIBLE__
  abs (Offset x)      = Offset $ abs x
  abs Infinity        = Infinity
  signum (Offset x)   = Offset $ signum x
  signum Infinity     = Offset $ 1
  fromInteger x       = Offset (fromInteger x)
  x * y = __IMPOSSIBLE__

instance Plus Weight Offset Weight where
  plus w k = w + (Offset k)

-- | Test for negativity, used to detect negative cycles.
class Negative a where
  negative :: a -> Bool

{- leads to Undecidable/OverlappingInstances:
instance (Ord a, Num a) => Negative a where
  negative = (< 0)
-}

instance Negative Int where
  negative = (< 0)

instance Negative Offset where
  negative (O x) = negative x

instance Negative Weight where
  negative Infinity = False
  negative (Offset x) = negative x

-- * Edge labels

-- | Going from @Lt@ to @Le@ is @pred@, going from @Le@ to @Lt@ is @succ@.
--
--   @X --(R,n)--> Y@
--   means  @X (R) Y + n@.
--   [                      ... if @n@ positive
--     and    @X + (-n) (R) Y@  if @n@ negative. ]
data Label
  = Label { lcmp :: Cmp, loffset :: Offset }
  | LInf  -- ^ Nodes not connected.


-- | Convert a label to a weight, decrementing in case of 'Lt'.
toWeight :: Label -> Weight
toWeight (Label Le w) = Offset w
toWeight (Label Lt w) = Offset $ pred w
toWeight LInf         = Infinity

instance Negative Label where
  negative = negative . toWeight

instance Eq Label where
  Label cmp w == Label cmp' w' = cmp == cmp' && w == w'
  LInf        == LInf          = True
  _           == _             = False

instance Ord Label where
  Label Lt  w <= Label Lt w' = w <= w'
  Label Le  w <= Label Le w' = w <= w'
  Label Lt  w <= Label Le w' = pred w <= w'
  Label Le  w <= Label Lt w' = succ w <= w'
  _           <= LInf        = True
  LInf{}      <= Label{}     = False

instance Show Label where
  show (Label cmp w) = show cmp ++ show w
  show LInf          = "∞"

instance MeetSemiLattice Label where
  -- one label is neutral
  LInf       `meet` l           = l
  l          `meet` LInf        = l
  -- other cases
  Label Lt w `meet` Label Lt w' = Label Lt $ w      `meet` w'
  Label Le w `meet` Label Le w' = Label Le $ w      `meet` w'
  Label Lt w `meet` Label Le w' = Label Lt $      w `meet` succ w'
  Label Le w `meet` Label Lt w' = Label Lt $ succ w `meet` w'

instance Top Label where
  top                 = LInf
  isTop Label{}       = False
  isTop LInf          = True

-- * Semiring with idempotent '+' == dioid

instance Dioid Weight where
  compose     = (+)
  unitCompose = 0

instance Dioid Label where
  compose (Label Lt w) (Label Lt w')    = Label Lt $ pred $ w + w'
  compose (Label cmp w) (Label cmp' w') = Label (compose cmp cmp') $ w + w'
  compose _             LInf            = LInf
  compose LInf          _               = LInf
  unitCompose = Label Le 0

-- * Graphs

-- ** Nodes

data Node rigid flex
  = NodeZero
  | NodeInfty
  | NodeRigid rigid
  | NodeFlex  flex
  deriving (Eq, Ord)

instance (Show rigid, Show flex) => Show (Node rigid flex) where
  show NodeZero      = "0"
  show NodeInfty     = "∞"
  show (NodeRigid x) = show x
  show (NodeFlex  x) = show x

isFlexNode :: Node rigid flex -> Maybe flex
isFlexNode (NodeFlex x) = Just x
isFlexNode _            = Nothing

isZeroNode :: Node rigid flex -> Bool
isZeroNode NodeZero{} = True
isZeroNode _          = False

isInftyNode :: Node rigid flex -> Bool
isInftyNode NodeInfty{} = True
isInftyNode _           = False

nodeToSizeExpr :: Node rigid flex -> SizeExpr' rigid flex
nodeToSizeExpr n =
  case n of
    NodeZero    -> Const 0
    NodeInfty   -> Infty
    NodeRigid i -> Rigid i 0
    NodeFlex x  -> Flex x 0

-- ** Edges

-- | An edge is negative if its label is.
instance Negative a => Negative (Edge' r f a) where
  negative = negative . label

-- instance Show a => Show (Edge' a) where
--   show (Edge u v l) = show u ++ " -(" ++ show l ++ ")-> " ++ show v

instance (Ord r, Ord f, MeetSemiLattice a) => MeetSemiLattice (Edge' r f a) where
  e@(Edge u v l) `meet` e'@(Edge u' v' l')
    | u == u' && v == v' = Edge u v $ l `meet` l'
    | otherwise          = __IMPOSSIBLE__
       -- error $ show e ++ " `meet` " ++ show e'

instance (Ord r, Ord f, Top a) => Top (Edge' r f a) where
  top = __IMPOSSIBLE__
  isTop e = isTop (label e)

instance (Ord r, Ord f, Dioid a) => Dioid (Edge' r f a) where
  e@(Edge u v l) `compose` e'@(Edge v' w l')
   | v == v'    = Edge u w $ l `compose` l'
   | otherwise = __IMPOSSIBLE__
      -- error $ show e ++ " `compose` " ++ show e'
  unitCompose  = __IMPOSSIBLE__

-- ** Graphs

-- | A graph forest.
type Graphs r f a = [Graph r f a]

emptyGraphs :: Graphs r f a
emptyGraphs = []

-- | Split a list of graphs @gs@ into those that mention node @n@ and those that do not.
--   If @n@ is zero or infinity, we regard it as "not mentioned".
mentions :: (Ord r, Ord f) => Node r f -> Graphs r f a -> (Graphs r f a, Graphs r f a)
mentions NodeZero    gs = ([], gs)
mentions NodeInfty   gs = ([], gs)
mentions NodeRigid{} gs = ([], gs)
mentions n           gs = partition (Set.member n . nodes) gs

-- | Add an edge to a graph forest.
--   Graphs that share a node with the edge are joined.
addEdge :: (Ord r, Ord f, MeetSemiLattice a, Top a) => Edge' r f a -> Graphs r f a -> Graphs r f a
addEdge e@(Edge src dest l) gs =
  -- Note: If we started from an empty forest
  -- and only added edges via @addEdge@, then
  -- @gsSrc@ and @gsDest@ contain each at most one graph.
  let (gsSrc , gsNotSrc)  = mentions src  gs
      (gsDest, gsNotDest) = mentions dest gsNotSrc
  in insertEdge e (Graph.unionsWith meet $ gsSrc ++ gsDest) : gsNotDest

-- | Reflexive closure.  Add edges @0 -> n -> n -> oo@ for all nodes @n@.
reflClos :: (Ord r, Ord f, Dioid a) => Set (Node r f) -> Graph r f a -> Graph r f a
reflClos ns g = setFoldl step g ns' where
    -- have at least the nodes in @ns@
    ns'      = nodes g `Set.union` ns
    -- add the trivial edges for all nodes ns'
    step g n = foldl (flip insertEdge) g es where
      es = [ Edge NodeZero n  unitCompose
           , Edge n        n  unitCompose
           , Edge n NodeInfty unitCompose
           ]

-- UNUSED
-- -- | Reflexive-transitive closure.
-- complete :: (Show a, Dioid a) => Graph r f a -> Graph r f a
-- complete = transClos . reflClos

-- | A graph is 'negative' if it contains a negative loop (diagonal edge).
--   Makes sense on transitive graphs.
instance (Ord r, Ord f, Negative a) => Negative (Graph r f a) where
  negative = any negative . Graph.diagonal

instance (Ord r, Ord f, Negative a) => Negative (Graphs r f a) where
  negative = any negative

-- | @h `implies` g@ if any edge in @g@ between rigids and constants
--   is implied by a corresponding edge in @h@, which means that
--   the edge in @g@ carries at most the information of the one in @h@.
--
--   Application: Constraint implication: Constraints are compatible
--   with hypotheses.
implies :: (Ord r, Ord f, Show r, Show f, Show a, Top a, Ord a, Negative a)
  => Graph r f a -> Graph r f a -> Bool
-- iterate 'test' over all edges in g
implies h g = and $ map test $ graphToList g
  -- NB: doing the @test k l@ before the recursive @b@ gives
  -- opportunity to short-cut the conjunction @&&@.
  where
    -- test :: Key -> a -> Bool
    test k@(Edge src dest l)
      | isZeroNode src, not (negative l) = True
      | isInftyNode dest                 = True
      | isJust $ isFlexNode src          = True
      | isJust $ isFlexNode dest         = True
      | isTop l                          = True
      | otherwise = case lookupEdge h src dest of
        Nothing -> False
        Just l' -> if l' <= l then True else
          trace ("edge " ++ show (l <$ k) ++ " not implied by " ++ show (l' <$ k)) $
            False
-- implies h g = Map.foldlWithKey (\ b k l -> test k l && b) True g
--   -- NB: doing the @test k l@ before the recursive @b@ gives
--   -- opportunity to short-cut the conjunction @&&@.
--   where
--     -- test :: Key -> a -> Bool
--     test k@(Edge src dest ()) l
--       | isZeroNode src, not (negative l) = True
--       | isInftyNode dest                 = True
--       | isJust $ isFlexNode src          = True
--       | isJust $ isFlexNode dest         = True
--       | isTop l                          = True
--       | otherwise = case lookupEdge h src dest of
--         Nothing -> False
--         Just l' -> if l' <= l then True else
--           trace ("edge " ++ show (l <$ k) ++ " not implied by " ++ show (l' <$ k)) $
--             False

nodeFromSizeExpr :: SizeExpr' rigid flex -> (Node rigid flex, Offset)
nodeFromSizeExpr e = case e of
  Const   n -> (NodeZero   , n)
  Rigid i n -> (NodeRigid i, n)
  Flex  x n -> (NodeFlex x , n)
  Infty     -> (NodeInfty  , 0)

edgeFromConstraint :: Constraint' rigid flex -> LabelledEdge rigid flex
edgeFromConstraint (Constraint lexp cmp rexp) =
  let (leftNode , n) = nodeFromSizeExpr lexp
      (rightNode, m) = nodeFromSizeExpr rexp
  in Edge leftNode rightNode (Label cmp $ m - n)

-- | Build a graph from list of simplified constraints.
graphFromConstraints :: (Ord rigid, Ord flex) => [Constraint' rigid flex] -> Graph rigid flex Label
graphFromConstraints cs =
  let -- convert to edges
      edges = map edgeFromConstraint cs
      -- build a graph from the edges
      g     = foldl (flip insertEdge) Graph.empty edges
  in  g

-- | Build a graph from list of simplified constraints.
graphsFromConstraints :: (Ord rigid, Ord flex) => [Constraint' rigid flex] -> Graphs rigid flex Label
graphsFromConstraints cs =
  let -- convert to edges
      edges = map edgeFromConstraint cs
      -- get all the flexibles mentioned in constraints
      xs    = Set.toList $ flexs cs
      -- for each flexible X, add edges 0 <= X and X <= oo
      fedges = concat $ for xs $ \ x ->
        [ Edge NodeZero (NodeFlex x) (Label Le 0)
        , Edge (NodeFlex x) NodeInfty (Label Le 0)
        ]
      -- build a graph from the edges
      gs    = foldl (flip addEdge) emptyGraphs (fedges ++ edges)
  in  gs

-- Build hypotheses graph, complete it, check for negative loops.

type Hyp = Constraint
type Hyp' = Constraint'
type HypGraph r f = Graph r f Label

hypGraph :: (Ord rigid, Ord flex, Show rigid, Show flex) =>
  Set rigid -> [Hyp' rigid flex] -> Either String (HypGraph rigid flex)
hypGraph is hyps0 = do
  -- get a list of hypothesis from a list of constraints
  hyps <- concat <$> mapM (simplify1 $ \ c -> return [c]) hyps0
  let g = transClos $
            reflClos (Set.mapMonotonic NodeRigid is) $
              graphFromConstraints hyps
  when (negative g) $ Left "size hypotheses graph has negative loop"
  return g

hypConn :: (Ord r, Ord f) => HypGraph r f -> Node r f -> Node r f -> Label
-- hypConn hg NodeZero n2  = Label Le 0  -- WRONG: not the best information
-- hypConn hg n1 NodeInfty = Label Le 0
hypConn hg n1 n2
  | n1 == n2                                = Label Le 0
  | Just l <- lookupEdge hg n1 n2 = l
  | otherwise                               = top

simplifyWithHypotheses :: (Ord rigid, Ord flex, Show rigid, Show flex) =>
  HypGraph rigid flex -> [Constraint' rigid flex] -> Either String [Constraint' rigid flex]
simplifyWithHypotheses hg cons = concat <$> mapM (simplify1 test) cons
  where
    -- Test whether a constraint is compatible with the hypotheses:
    -- Succeeds, if constraint is implied by hypotheses,
    -- fails otherwise.
    test c = do
      let Edge n1 n2 l = edgeFromConstraint c
          l' = hypConn hg n1 n2
      -- l' <- lookupEdge hg n1 n2
      unless (l' <= l) $ Left $
        "size constraint " ++ show c ++ " not consistent with size hypotheses"
      return [c]
      -- if (l' <= l) then Just [c] else Nothing

-- Build constraint graph, complete it, check for negative loops.
-- Check that hypotheses graph implies constraint graphs (rigids).

type ConGraph r f = Graph r f Label

constraintGraph :: (Ord r, Ord f, Show r, Show f) => [Constraint' r f] -> HypGraph r f -> Either String (ConGraph r f)
constraintGraph cons0 hg = do
  traceM $ "original constraints cons0 = " ++ show cons0
  -- Simplify constraints, ensure they are locally consistent with
  -- hypotheses.
  cons <- simplifyWithHypotheses hg cons0
  traceM $ "simplified constraints cons = " ++ show cons
  -- Build a transitive graph from constraints.
  let g = transClos $ graphFromConstraints cons
  traceM $ "transitive graph g = " ++ show (graphToList g)
  -- Ensure it has no negative loops.
  when (negative g) $ Left $
    "size constraint graph has negative loops"
  -- Ensure it does not constrain the hypotheses.
  unless (hg `implies` g) $ Left $
    "size constraint graph constrains size hypotheses"
  return g

type ConGraphs r f = Graphs r f Label

constraintGraphs :: (Ord r, Ord f, Show r, Show f) => [Constraint' r f] -> HypGraph r f -> Either String ([f], ConGraphs r f)
constraintGraphs cons0 hg = do
  traceM $ "original constraints cons0 = " ++ show cons0
  -- Simplify constraints, ensure they are locally consistent with
  -- hypotheses.
  cons <- simplifyWithHypotheses hg cons0
  traceM $ "simplified constraints cons = " ++ show cons
  -- Build a transitive graph forest from constraints.
  let gs0 = graphsFromConstraints cons
  traceM $ "constraint forest gs0 = " ++ show (map graphToList gs0)
  let gs1 = map transClos gs0
  traceM $ "transitive forest gs1 = " ++ show (map graphToList gs1)
  -- Check for flexibles to be set to infinity
  let (xss,gs) = unzip $ map infinityFlexs gs1
      xs       = concat xss
  unless (null xs) $ do
    traceM $ "flexibles to set to oo = " ++ show xs
    traceM $ "forest after oo-subst  = " ++ show (map graphToList gs)
  -- Ensure none has negative loops.
  when (negative gs) $ Left $ "size constraint graph has negative loop"
  traceM $ "we are free of negative loops"
  -- Ensure it does not constrain the hypotheses.
  forM_ gs $ \ g -> unless (hg `implies` g) $ Left $
    "size constraint graph constrains size hypotheses"
  traceM $ "any constraint between rigids is implied by the hypotheses"
  return (xs, gs)

-- | If we have an edge @X + n <= X@ (with n >= 0), we must set @X = oo@.
infinityFlexs :: (Ord r, Ord f) => ConGraph r f -> ([f], ConGraph r f)
infinityFlexs g = (infFlexs, setToInfty infFlexs g)
  where
    -- get the flexibles that need to be set to infinity
    infFlexs = mapMaybe flexNeg $ Graph.diagonal g
    flexNeg e = do
      guard $ negative e
      isFlexNode (src e)

class SetToInfty f a where
  setToInfty :: [f] -> a -> a

instance (Eq f) => SetToInfty f (Node r f) where
  setToInfty xs (NodeFlex x) | x `elem` xs = NodeInfty
  setToInfty xs n = n

instance (Eq f) => SetToInfty f (Edge' r f a) where
  setToInfty xs (Edge n1 n2 l) = Edge (setToInfty xs n1) (setToInfty xs n2) l

instance (Ord r, Ord f) => SetToInfty f (ConGraph r f) where
  setToInfty xs = graphFromList . filter h . map (setToInfty xs) . graphToList
    where
      -- filter out edges @oo + k <= oo@
      h (Edge NodeInfty NodeInfty (Label Le _)) = False
      h _ = True


-- * Compute solution from constraint graph.

instance Plus Offset Weight Weight where
  plus e Infinity   = Infinity
  plus e (Offset x) = Offset $ plus e x

instance Plus (SizeExpr' r f) Weight (SizeExpr' r f) where
  plus e Infinity   = Infty
  plus e (Offset x) = plus e x

instance Plus (SizeExpr' r f) Label (SizeExpr' r f) where
  plus e l = plus e (toWeight l)

-- | Lower or upper bound for a flexible variable
type Bound r f = Map f (Set (SizeExpr' r f))

emptyBound :: Bound r f
emptyBound = Map.empty

data Bounds r f = Bounds
  { lowerBounds :: Bound r f
  , upperBounds :: Bound r f
  , mustBeFinite :: Set f
    -- ^ These metas are < ∞.
  }

-- | Compute a lower bound for a flexible from an edge.
edgeToLowerBound :: LabelledEdge r f -> Maybe (f, SizeExpr' r f)
edgeToLowerBound e =
  case e of
    (Edge n1 n2 LInf) -> __IMPOSSIBLE__
    (Edge NodeZero (NodeFlex x) (Label Le o)) | o >= 0 -> Just (x, Const 0)
    (Edge NodeZero (NodeFlex x) (Label Lt o)) | o >= 1 -> Just (x, Const 0)
    (Edge n1 (NodeFlex x) l) -> Just (x, nodeToSizeExpr n1 `plus` (- (toWeight l)))
    _ -> Nothing

-- | Compute an upper bound for a flexible from an edge.
edgeToUpperBound :: LabelledEdge r f -> Maybe (f, Cmp, SizeExpr' r f)
edgeToUpperBound e =
  case e of
    (Edge n1 n2 LInf) -> __IMPOSSIBLE__
    (Edge n1           NodeInfty (Label Le _)) -> Nothing
    (Edge (NodeFlex x) NodeInfty (Label Lt _)) -> Just (x, Lt, Infty)
    (Edge (NodeFlex x) n2        l           ) -> Just (x, Le, nodeToSizeExpr n2 `plus` (toWeight l))
    _ -> Nothing

-- | Compute the lower bounds for all flexibles in a graph.
graphToLowerBounds :: (Ord r, Ord f) => [LabelledEdge r f] -> Bound r f
graphToLowerBounds = flip foldl emptyBound $ \ bs e ->
  case edgeToLowerBound e of
    Nothing          -> bs
    Just (x, Flex{}) -> bs  -- ignore flexible bounds
    Just (x, a)      -> Map.insertWith Set.union x (Set.singleton a) bs

-- | Compute the upper bounds for all flexibles in a graph.
graphToUpperBounds :: (Ord r, Ord f) => [LabelledEdge r f] -> (Bound r f, Set f)
graphToUpperBounds = flip foldl (emptyBound, Set.empty) $ \ (bs, fs) e ->
  case edgeToUpperBound e of
    Nothing             -> (bs, fs)
    Just (x, _, Flex{}) -> (bs, fs)  -- ignore flexible bounds
    Just (x, Lt, Infty) -> (bs, Set.insert x fs)
    Just (x, Le, a)     -> (Map.insertWith Set.union x (Set.singleton a) bs, fs)
    _                   -> __IMPOSSIBLE__

-- | Compute the bounds for all flexibles in a graph.
bounds :: (Ord r, Ord f) => ConGraph r f -> Bounds r f
bounds g = Bounds lbs ubs fs
  where edges     = graphToList g
        lbs       = graphToLowerBounds edges
        (ubs, fs) = graphToUpperBounds edges


-- | Compute the relative minima in a set of nodes (those that do not have
--   a predecessor in the set).
smallest ::(Ord r, Ord f) => HypGraph r f -> [Node r f] -> [Node r f]
smallest hg ns
  | NodeZero `elem` ns = [NodeZero]
  | otherwise          = filter hasNoPred ns where
      hasNoPred NodeInfty = False
      hasNoPred n = null $ mapMaybe strictEdge ns where
        -- is there an edge n -l-> n' with l <= 0
        strictEdge n' = do
          guard (n /= n')  -- exclude loops
          l <- lookupEdge hg n' n
          guard (toWeight l <= 0)
          return ()

-- | Compute the relative maxima in a set of nodes (those that do not have
--   a successor in the set).
largest ::(Ord r, Ord f) => HypGraph r f -> [Node r f] -> [Node r f]
largest hg ns
  | NodeInfty `elem` ns = [NodeInfty]
  | otherwise          = filter hasNoSucc ns where
      hasNoSucc NodeZero = False
      hasNoSucc n = null $ mapMaybe strictEdge ns where
        -- is there an edge n -l-> n' with l <= 0
        strictEdge n' = do
          guard (n /= n')  -- exclude loops
          l <- lookupEdge hg n n'
          guard (toWeight l <= 0)
          return ()

{-|  Given source nodes n1,n2,... find all target nodes m1,m2, such
     that for all j, there are edges  n_i --l_ij--> m_j  for all i.
     Return these edges as a map from target notes to a list of edges.
     We assume the graph is reflexive-transitive.
 -}
commonSuccs :: (Ord r, Ord f) =>
               Graph r f a -> [Node r f] -> Map (Node r f) [Edge' r f a]
commonSuccs hg srcs = intersectAll $ map (buildmap . outgoing hg) srcs
  where
   buildmap            = Map.fromList . map (\ e -> (dest e, [e]))
   intersectAll []     = Map.empty
   intersectAll (m:ms) = foldl (Map.intersectionWith (++)) m ms

{-|  Given target nodes m1,m2,... find all source nodes n1,n2, such
     that for all j, there are edges  n_i --l_ij--> m_j  for all i.
     Return these edges as a map from target notes to a list of edges.
     We assume the graph is reflexive-transitive.
 -}
commonPreds :: (Ord r, Ord f) => Graph r f a -> [Node r f] -> Map (Node r f) [Edge' r f a]
commonPreds hg tgts = intersectAll $  map (buildmap . incoming hg) tgts
  where
   buildmap = Map.fromList . map (\ e -> (src e, [e]))
   intersectAll []     = Map.empty
   intersectAll (m:ms) = foldl (Map.intersectionWith (++)) m ms

-- | Compute the sup of two different rigids or a rigid and a constant.
lub' :: forall r f . (Ord r, Ord f, Show r, Show f) =>
        HypGraph r f -> (Node r f, Offset) -> (Node r f, Offset) -> Maybe (SizeExpr' r f)
lub' hg (node1, n) (node2, m) = do
  let sucs     = commonSuccs hg [node1, node2]
      sucNodes = smallest hg $ Map.keys sucs
  traceM ("lub': sucs = " ++ show sucs)
  case sucNodes of
    -- there is a unique smallest common successor n0 of node1 and node2
    [n0] -> do
      -- then there are exactly two edges node1 --l1--> n0 and node2 --l2--> n0
      -- Andreas, 2017-04-28, issue #2558: The following invariant does not hold always
      -- -- with non-positive weights l1, l2
      let es = fromMaybe __IMPOSSIBLE__ $ Map.lookup n0 sucs
      case es of
        [ Edge node1x n1 l1 ,
          Edge node2x n2 l2 ] -> do
          unless (n0 == n1)         __IMPOSSIBLE__
          unless (n0 == n2)         __IMPOSSIBLE__
          unless (node1 == node1x)  __IMPOSSIBLE__
          unless (node2 == node2x)  __IMPOSSIBLE__
          -- Andreas, 2017-04-28, issue #2558: The following invariant does not hold always
          -- unless (toWeight l1 <= 0) __IMPOSSIBLE__
          -- unless (toWeight l2 <= 0) __IMPOSSIBLE__
          let o :: Weight
              o = max (n `plus` toWeight l1) (m `plus` toWeight l2)
          return $ nodeToSizeExpr n0 `plus` o
        _ -> __IMPOSSIBLE__
    -- otherwise, we cannot compute the sup
    _ -> do
      let a1 :: SizeExpr' r f = nodeToSizeExpr node1 `plus` n
      let a2 :: SizeExpr' r f = nodeToSizeExpr node2 `plus` m
      traceM ("cannot compute lub of " ++ show a1 ++ " and " ++ show a2 ++ " because sucNodes = " ++ show sucNodes)
      Nothing

-- | Compute the inf of two different rigids or a rigid and a constant.
glb' :: forall r f . (Ord r, Ord f, Show r, Show f) => HypGraph r f -> (Node r f, Offset) -> (Node r f, Offset) -> Maybe (SizeExpr' r f)
glb' hg (node1, n) (node2, m) = do
  let preds     = commonPreds hg [node1, node2]
      predNodes = largest hg $ Map.keys preds
  traceM ("glb': preds = " ++ show preds)
  case predNodes of
    -- there is a unique greatest common predecessor n0 of node1 and node2
    [n0] -> do
      -- then there are exactly two edges n0 --l1--> node1 and n0 --l2--> node2
      -- Andreas, 2017-04-28, issue #2558: The following invariant may not hold always
      -- -- with non-positive weigths l1, l2
      let es = fromMaybe __IMPOSSIBLE__ $ Map.lookup n0 preds
      case es of
        [ Edge n1 node1x l1 ,
          Edge n2 node2x l2] -> do
          unless (n0 == n1)         __IMPOSSIBLE__
          unless (n0 == n2)         __IMPOSSIBLE__
          unless (node1 == node1x)  __IMPOSSIBLE__
          unless (node2 == node2x)  __IMPOSSIBLE__
          -- Andreas, 2017-04-28, issue #2558: The following invariant may not hold always
          -- unless (toWeight l1 <= 0) __IMPOSSIBLE__
          -- unless (toWeight l2 <= 0) __IMPOSSIBLE__
          let o :: Weight
              o = max (n `plus` toWeight l1) (m `plus` toWeight l2)
          return $ nodeToSizeExpr n0 `plus` o
        _ -> __IMPOSSIBLE__
    -- otherwise, we cannot compute the sup
    _ -> do
      let a1 :: SizeExpr' r f = nodeToSizeExpr node1 `plus` n
      let a2 :: SizeExpr' r f = nodeToSizeExpr node2 `plus` m
      traceM ("cannot compute glb of " ++ show a1 ++ " and " ++ show a2 ++ " because predNodes = " ++ show predNodes)
      Nothing

-- | Compute the least upper bound (sup).
lub :: (Ord r, Ord f, Show r, Show f) => HypGraph r f -> (SizeExpr' r f) -> (SizeExpr' r f) -> Maybe (SizeExpr' r f)
lub hg a1 a2 =
  case (a1, a2) of
    (Flex{}, _)   -> __IMPOSSIBLE__
    (_, Flex{})   -> __IMPOSSIBLE__
    (Infty, a2)   -> Just Infty
    (a1, Infty)   -> Just Infty
    (Const n  , Const m  )
                  -> Just $ Const $ max n m
    (Const n  , Rigid j m)
      | m >= n    -> Just a2
      | otherwise -> lub' hg (NodeZero, n) (NodeRigid j, m)
    (Rigid i n, Const m  )
      | n >= m    -> Just a1
      | otherwise -> lub' hg (NodeRigid i, n) (NodeZero, m)
    (Rigid i n, Rigid j m)
      | i == j    -> Just $ Rigid i $ max n m
      | otherwise -> lub' hg (NodeRigid i, n) (NodeRigid j, m)

{- Finding the glb of two rigid size expressions in hypotheses graph

  a1 = Rigid i n
  a2 = Rigid j m

  Find the topological predecessors of (NodeRigid i)
  Find the topological predecessors of (NodeRigid j)

-}

-- | Compute the greatest lower bound (inf) of size expressions relative
--   to a hypotheses graph.
glb :: (Ord r, Ord f, Show r, Show f) => HypGraph r f -> (SizeExpr' r f) -> (SizeExpr' r f) -> Maybe (SizeExpr' r f)
glb hg a1 a2 =
  case (a1, a2) of
    (Flex{}, _) -> __IMPOSSIBLE__
    (_, Flex{}) -> __IMPOSSIBLE__
    (Infty, a2) -> Just a2
    (a1, Infty) -> Just a1
    (Const n  , Const m  )          -> Just $ Const $ min n m
    (Const n  , Rigid i m)
      | n <= m    -> Just a1
      | otherwise -> glb' hg (NodeZero, n) (NodeRigid i, m)
    (Rigid i n, Const m  )
      | m <= n    -> Just a2
      | otherwise -> glb' hg (NodeRigid i, n) (NodeZero, m)
    (Rigid i n, Rigid j m)
      | i == j    -> Just $ Rigid i $ min n m
      | otherwise -> glb' hg (NodeRigid i, n) (NodeRigid j, m)
{-
    (Rigid i n, Rigid j m) -> do
      let iLeqj = Map.lookup (Edge (NodeRigid i) (NodeRigid j) ()) hg
          jLeqi = Map.lookup (Edge (NodeRigid j) (NodeRigid i) ()) hg
      case (iLeqj, jLeqi) of
        (Nothing, Nothing) -> Nothing -- maximum as size expression
        (Just l, Nothing) | Offset k <- toWeight l ->
          if k + n <= m then Just a1
          else Nothing -- no guaranteed infimum
        (Nothing, Just l) | Offset k <- toWeight l ->
          if k + m <= n then Just a2
          else Nothing
        (Just{}, Just{}) -> Nothing
{-
      let lbi = incoming hg (NodeRigid i)
          lbj = incoming hg (NodeRigid j)
          srci = Set.fromList $ map src lbi
          srcj = Set.fromList $ map src lbj
          srcs =  Set.intersection srci srcj
-}
    _ -> trace ("cannot compute glb of " ++ show a1 ++ " and " ++ show a2) $
      Nothing -- TODO!
-}

findRigidBelow :: (Ord r, Ord f) => HypGraph r f -> (SizeExpr' r f) -> Maybe (SizeExpr' r f)
findRigidBelow hg (Rigid i m) | m < 0 = do
  let v     = NodeRigid i
      preds = incoming hg v
      filt e@(Edge n n' l)
        | n' == v   =
          case toWeight l of
            Infinity -> Nothing
            Offset o -> if o <= m then Just (n, o) else Nothing
        | otherwise = __IMPOSSIBLE__
            -- error $ "findRigidBelow: impossible: " ++ show e
      cands = mapMaybe filt preds
  (n, o) <- do
    case cands of
      []  -> Nothing
      [c] -> return c
      _   -> return $
               maximumBy (compare `on` snd) $
                 filter ((NodeZero /=) . fst) cands
  let offset = m - o
  unless (offset >= 0) __IMPOSSIBLE__
  return $ nodeToSizeExpr n `plus` offset
findRigidBelow hg e = __IMPOSSIBLE__
  -- error $ "findRigidBelow: impossible: " ++ show e


solveGraph :: (Ord r, Ord f, Show r, Show f) => Polarities f -> HypGraph r f -> ConGraph r f -> Either String (Solution r f)
solveGraph pols hg g = do
  let (Bounds lbs ubs fs) = bounds g
      -- flexibles to solve for
      xs = Set.toAscList $ Set.unions [ Map.keysSet lbs, Map.keysSet ubs, fs ]
  -- iterate over all flexible variables
  xas <- catMaybes <$> do
    forM xs $ \ x -> do
      -- get lower and upper bounds for flexible x
      let lx = Set.toList $ Map.findWithDefault Set.empty x lbs
          ux = Set.toList $ Map.findWithDefault Set.empty x ubs
      traceM ("lower bounds for " ++ show x ++ ": " ++ show lx)
      traceM ("upper bounds for " ++ show x ++ ": " ++ show ux)
      -- compute maximum of lower bounds
      lb <- do
        case lx of
          []     -> return $ Nothing
          (a:as) -> do
            case foldM (lub hg) a as of
              Nothing -> Left $ "inconsistent lower bound for " ++ show x
              Just l  -> return $ Just $ truncateOffset l
      -- compute minimum of upper bounds
      ub <- do
        case ux of
          []     -> return $ Nothing
          (a:as) -> do
            case foldM (glb hg) a as of
              Just l | validOffset l                  -> return $ Just l
                     | Just l' <- findRigidBelow hg l -> return $ Just l'
              _ -> Left $ "inconsistent upper bound for " ++ show x
      case (lb, ub) of
        (Just l, Nothing) -> return $ Just (x, l)  -- solve x = lower bound
        (Nothing, Just u) -> return $ Just (x, u)  -- solve x = upper bound
        (Just l,  Just u) -> do
          traceM ("lower bound for " ++ show x ++ ": " ++ show l)
          traceM ("upper bound for " ++ show x ++ ": " ++ show u)
          case getPolarity pols x of
            Least    -> return $ Just (x, l)
            Greatest -> return $ Just (x, u)
        _ -> return Nothing
  return $ Map.fromList xas

-- | Solve a forest of constraint graphs relative to a hypotheses graph.
--   Concatenate individual solutions.
solveGraphs :: (Ord r, Ord f, Show r, Show f) => Polarities f -> HypGraph r f -> ConGraphs r f -> Either String (Solution r f)
solveGraphs pols hg gs = Map.unions <$> mapM (solveGraph pols hg) gs

-- * Verify solution

-- | Check that after substitution of the solution,
--   constraints are implied by hypotheses.
verifySolution :: (Ord r, Ord f, Show r, Show f) => HypGraph r f -> [Constraint' r f] -> Solution r f -> Either String ()
verifySolution hg cs sol = do
  cs <- return $ subst sol cs
  traceM $ "substituted constraints " ++ show cs
  cs <- -- maybe (Left "solution produces inconsistency") Right $
          concat <$> mapM (simplify1 $ \ c -> return [c]) cs
  traceM $ "simplified substituted constraints " ++ show cs
  -- cs <- maybe (Left "solution produces inconsistency") Right $
  --         simplifyWithHypotheses hg cs
  let g = graphFromConstraints cs
  unless (hg `implies` g) $
    Left "solution not implied by hypotheses"
{-
  case simplifyWithHypotheses hg $ subst sol cs of
    Nothing -> Left "solution produces inconsistency"
    Just [] -> Right ()
    Just cs -> Left $ "solution leaves constraints " ++ show cs
-}

-- | Iterate solver until no more metas can be solved.
--
--   This might trigger a (wanted) error on the second iteration (see Issue 2096)
--   which would otherwise go unnoticed.

iterateSolver
  :: (Ord r, Ord f, Show r, Show f)
  => Polarities f
     -- ^ Meta variable polarities (prefer lower or upper solution?).
  -> HypGraph r f
     -- ^ Hypotheses (assumed to have no metas, so, fixed during iteration).
  -> [Constraint' r f]
     -- ^ Constraints to solve.
  -> Solution r f
     -- ^ Previous substitution (already applied to constraints).
  -> Either String (Solution r f)
     -- ^ Accumulated substition.

iterateSolver pols hg cs sol0 = do
  g <- constraintGraph cs hg
  sol <- solveGraph pols hg g
  traceM $ "(partial) solution " ++ show sol
  if Map.null sol then return sol0 else
    iterateSolver pols hg (subst sol cs) (Map.unionWith __IMPOSSIBLE__ sol $ subst sol sol0)

-- * Tests

testSuccs :: Ord f => Map (Node [Char] f) [Edge' [Char] f Label]
testSuccs = commonSuccs hg [n1,n2]
  where
    n1 = NodeRigid "i"
    n2 = NodeRigid "j"
    n3 = NodeRigid "k"
    n4 = NodeRigid "l"
    n5 = NodeRigid "m"
    hg = Graph.fromList
         [ Graph.Edge n1 n3 $ Label Le 1
         , Graph.Edge n1 n4 $ Label Le 2
         , Graph.Edge n1 n5 $ Label Le 3
         , Graph.Edge n2 n3 $ Label Le 4
         , Graph.Edge n2 n4 $ Label Le 5
         , Graph.Edge n2 n5 $ Label Le 6
         ]

-- testLub = smallest hg $ Map.keys $ commonSuccs hg [n1,n2] --
testLub :: (Show f, Ord f) => Maybe (SizeExpr' [Char] f)
testLub = lub hg (Rigid "i" 0) (Rigid "j" 2)
  where
    n1 = NodeRigid "i"
    n2 = NodeRigid "j"
    n3 = NodeRigid "k"
    n4 = NodeRigid "l"
    n5 = NodeRigid "m"
    hg = Graph.fromList
         [ Graph.Edge n1 n3 $ Label Le 0
         , Graph.Edge n1 n4 $ Label Le 2
         , Graph.Edge n1 n5 $ Label Le 4
         , Graph.Edge n2 n3 $ Label Le 1
         , Graph.Edge n2 n4 $ Label Le 3
         , Graph.Edge n2 n5 $ Label Le 5
         , Graph.Edge n3 n4 $ Label Le 0
         , Graph.Edge n3 n5 $ Label Lt 0
         ]
