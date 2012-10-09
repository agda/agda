{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Agda.Utils.Warshall where

{- construct a graph from constraints

   x + n <= y   becomes   x ---(-n)---> y
   x <= n + y   becomes   x ---(+n)---> y

the default edge (= no edge is) labelled with infinity

building the graph involves keeping track of the node names.
We do this in a finite map, assigning consecutive numbers to nodes.
-}

import Control.Applicative
import Control.Monad.State
import Data.Maybe -- fromJust
import Data.Array
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Test.QuickCheck
import Agda.Utils.TestHelpers
import Agda.Syntax.Common
import Agda.Utils.QuickCheck
import Agda.Utils.SemiRing

import Debug.Trace

type Matrix a = Array (Int,Int) a

-- assuming a square matrix
warshall :: SemiRing a => Matrix a -> Matrix a
warshall a0 = loop r a0 where
  b@((r,c),(r',c')) = bounds a0 -- assuming r == c and r' == c'
  loop k a | k <= r' =
    loop (k+1) (array b [ ((i,j),
                           (a!(i,j)) `oplus` ((a!(i,k)) `otimes` (a!(k,j))))
                        | i <- [r..r'], j <- [c..c'] ])
           | otherwise = a

-- Warshall's algorithm on a graph represented as an adjacency list.
type AdjList node edge = Map node [(node, edge)]

warshallG :: (SemiRing edge, Ord node) => AdjList node edge -> AdjList node edge
warshallG g = fromMatrix $ warshall m
  where
    nodes = zip (nub $ Map.keys g ++ map fst (concat $ Map.elems g))
                [0..]
    len   = length nodes
    b     = ((0,0), (len - 1,len - 1))

    edge i j = do
      es <- Map.lookup i g
      foldr oplus Nothing [ Just v | (j', v) <- es, j == j' ]

    m = array b [ ((n, m), edge i j) | (i, n) <- nodes, (j, m) <- nodes ]

    fromMatrix matrix = Map.fromList $ do
      (i, n) <- nodes
      let es = [ (fst (nodes !! m), e)
               | m <- [0..len - 1]
               , Just e <- [matrix ! (n, m)]
               ]
      return (i, es)

-- edge weight in the graph, forming a semi ring

data Weight = Finite Int | Infinite
              deriving (Eq)

inc :: Weight -> Int -> Weight
inc Infinite   n = Infinite
inc (Finite k) n = Finite (k + n)

instance Show Weight where
  show (Finite i) = show i
  show Infinite   = "."

instance Ord Weight where
  a <= Infinite = True
  Infinite <= b = False
  Finite a <= Finite b = a <= b

instance SemiRing Weight where
  oplus = min

  otimes Infinite _ = Infinite
  otimes _ Infinite = Infinite
  otimes (Finite a) (Finite b) = Finite (a + b)

-- constraints ---------------------------------------------------

-- nodes of the graph are either
-- * flexible variables (with identifiers drawn from Int),
-- * rigid variables (also identified by Ints), or
-- * constants (like 0, infinity, or anything between)

data Node = Rigid Rigid
          | Flex  FlexId
            deriving (Eq, Ord)

data Rigid = RConst Weight
           | RVar RigidId
             deriving (Eq, Ord, Show)

type NodeId  = Int
type RigidId = Int
type FlexId  = Int
type Scope   = RigidId -> Bool
-- which rigid variables a flex may be instatiated to

instance Show Node where
  show (Flex  i) = "?" ++ show i
  show (Rigid (RVar i)) = "v" ++ show i
  show (Rigid (RConst Infinite))   = "#"
  show (Rigid (RConst (Finite n))) = show n

infinite (RConst Infinite) = True
infinite _ = False

-- isBelow r w r'
-- checks, if r and r' are connected by w (meaning w not infinite)
-- wether r + w <= r'
-- precondition: not the same rigid variable
isBelow :: Rigid -> Weight -> Rigid -> Bool
isBelow _ Infinite _ = True
isBelow _ n (RConst Infinite) = True
-- isBelow (RConst Infinite)   n (RConst (Finite _)) = False
isBelow (RConst (Finite i)) (Finite n) (RConst (Finite j)) = i + n <= j
isBelow _ _ _ = False -- rigid variables are not related

-- a constraint is an edge in the graph
data Constraint = NewFlex FlexId Scope
                | Arc Node Int Node
-- Arc v1 k v2  at least one of v1,v2 is a VMeta (Flex),
--              the other a VMeta or a VGen (Rigid)
-- if k <= 0 this means  $^(-k) v1 <= v2
-- otherwise                    v1 <= $^k v3

instance Show Constraint where
  show (NewFlex i s) = "SizeMeta(?" ++ show i ++ ")"
  show (Arc v1 k v2) | k == 0 = show v1 ++ "<=" ++ show v2
                     | k < 0  = show v1 ++ "+" ++ show (-k) ++ "<=" ++ show v2
                     | otherwise  = show v1 ++ "<=" ++ show v2 ++ "+" ++ show k

type Constraints = [Constraint]

emptyConstraints = []

-- graph (matrix) ------------------------------------------------

data Graph = Graph
  { flexScope :: Map FlexId Scope        -- scope for each flexible var
  , nodeMap :: Map Node NodeId           -- node labels to node numbers
  , intMap  :: Map NodeId Node           -- node numbers to node labels
  , nextNode :: NodeId                   -- number of nodes (n)
  , graph :: NodeId -> NodeId -> Weight  -- the edges (restrict to [0..n[)
  }

-- the empty graph: no nodes, edges are all undefined (infinity weight)
initGraph = Graph Map.empty Map.empty Map.empty 0 (\ x y -> Infinite)

-- the Graph Monad, for constructing a graph iteratively
type GM = State Graph

addFlex :: FlexId -> Scope -> GM ()
addFlex x scope = do
  st <- get
  put $ st { flexScope = Map.insert x scope (flexScope st) }
  addNode (Flex x)
  return ()


-- i <- addNode n  returns number of node n. if not present, it is added first
addNode :: Node -> GM Int
addNode n = do
  st <- get
  case Map.lookup n (nodeMap st) of
    Just i -> return i
    Nothing -> do let i = nextNode st
                  put $ st { nodeMap = Map.insert n i (nodeMap st)
                           , intMap = Map.insert i n (intMap st)
                           , nextNode = i + 1
                           }
                  return i

-- addEdge n1 k n2
-- improves the weight of egde n1->n2 to be at most k
-- also adds nodes if not yet present
addEdge :: Node -> Int -> Node -> GM ()
addEdge n1 k n2 = do
  i1 <- addNode n1
  i2 <- addNode n2
  st <- get
  let graph' x y = if (x,y) == (i1,i2) then Finite k `oplus` (graph st) x y
                   else graph st x y
  put $ st { graph = graph' }

addConstraint :: Constraint -> GM ()
addConstraint (NewFlex x scope) = addFlex x scope
addConstraint (Arc n1 k n2)     = addEdge n1 k n2

buildGraph :: Constraints -> Graph
buildGraph cs = execState (mapM_ addConstraint cs) initGraph

mkMatrix :: Int -> (Int -> Int -> Weight) -> Matrix Weight
mkMatrix n g = array ((0,0),(n-1,n-1))
                 [ ((i,j), g i j) | i <- [0..n-1], j <- [0..n-1]]

-- displaying matrices with row and column labels --------------------

-- a matrix with row descriptions in b and column descriptions in c
data LegendMatrix a b c = LegendMatrix
  { matrix   :: Matrix a
  , rowdescr :: Int -> b
  , coldescr :: Int -> c
  }

instance (Show a, Show b, Show c) => Show (LegendMatrix a b c) where
  show (LegendMatrix m rd cd) =
    -- first show column description
    let ((r,c),(r',c')) = bounds m
    in foldr (\ j s -> "\t" ++ show (cd j) ++ s) "" [c .. c'] ++
    -- then output rows
       foldr (\ i s -> "\n" ++ show (rd i) ++
                foldr (\ j t -> "\t" ++ show (m!(i,j)) ++ t)
                      (s)
                      [c .. c'])
             "" [r .. r']

-- solving the constraints -------------------------------------------

-- a solution assigns to each flexible variable a size expression
-- which is either a constant or a v + n for a rigid variable v
type Solution = Map Int SizeExpr

emptySolution = Map.empty
extendSolution subst k v = Map.insert k v subst

data SizeExpr = SizeVar RigidId Int   -- e.g. x + 5
              | SizeConst Weight  -- a number or infinity

instance Show SizeExpr where
  show (SizeVar n 0) = show (Rigid (RVar n))
  show (SizeVar n k) = show (Rigid (RVar n)) ++ "+" ++ show k
  show (SizeConst w) = show w

-- sizeRigid r n  returns the size expression corresponding to r + n
sizeRigid :: Rigid -> Int -> SizeExpr
sizeRigid (RConst k) n = SizeConst (inc k n)
sizeRigid (RVar i)   n = SizeVar i n

{-
apply :: SizeExpr -> Solution -> SizeExpr
apply e@(SizeExpr (Rigid _) _) phi = e
apply e@(SizeExpr (Flex  x) i) phi = case Map.lookup x phi of
  Nothing -> e
  Just (SizeExpr v j) -> SizeExpr v (i + j)

after :: Solution -> Solution -> Solution
after psi phi = Map.map (\ e -> e `apply` phi) psi
-}

{-
solve :: Constraints -> Maybe Solution
solve cs = if any (\ x -> x < Finite 0) d then Nothing
     else Map.
   where gr = buildGraph cs
         n  = nextNode gr
         m  = mkMatrix n (graph gr)
         m' = warshall m
         d  = [ m!(i,i) | i <- [0 .. (n-1)] ]
         ns = keys (nodeMap gr)
-}

{- compute solution

a solution CANNOT exist if

  v < v  for a rigid variable v

{- Andreas, 2012-09-19 OUTDATED
  v <= v' for rigid variables v,v'

  x < v   for a flexible variable x and a rigid variable v
-}

thus, for each flexible x, only one of the following cases is possible

  r+n <= x+m <= infty  for a unique rigid r  (meaning r --(m-n)--> x)
  x <= r+n             for a unique rigid r  (meaning x --(n)--> r)

we are looking for the least values for flexible variables that solve
the constraints.  Algorithm

while flexible variables and rigid rows left
  find a rigid variable row i
    for all flexible columns j
      if i --n--> j with n<=0 (meaning i+n <= j) then j = i + n

while flexible variables j left
  search the row j for entry i
    if j --n--> i with n >= 0 (meaning j <= i + n) then j = i + n

-}

solve :: Constraints -> Maybe Solution
solve cs = -- trace (show cs) $
   -- trace (show lm0) $
    -- trace (show lm) $ -- trace (show d) $
     let solution = if solvable then loop1 flexs rigids emptySolution
                    else Nothing
     in -- trace (show solution) $
         solution
   where -- compute the graph and its transitive closure m
         gr  = buildGraph cs
         n   = nextNode gr            -- number of nodes
         m0  = mkMatrix n (graph gr)
         m   = warshall m0

         -- tracing only: build output version of transitive graph
         legend i = fromJust $ Map.lookup i (intMap gr) -- trace only
         lm0 = LegendMatrix m0 legend legend            -- trace only
         lm  = LegendMatrix m legend legend             -- trace only

         -- compute the sets of flexible and rigid node numbers
         ns  = Map.keys (nodeMap gr)
         -- a set of flexible variables
         flexs  = foldl' (\ l k -> case k of (Flex i) -> i : l
                                             (Rigid _) -> l) [] ns
         -- a set of rigid variables
         rigids = foldl' (\ l k -> case k of (Flex _) -> l
                                             (Rigid i) -> i : l) [] ns

         -- rigid matrix indices
         rInds = foldl' (\ l r -> let Just i = Map.lookup (Rigid r) (nodeMap gr)
                                  in i : l) [] rigids

         -- check whether there is a solution
         -- d   = [ m!(i,i) | i <- [0 .. (n-1)] ]  -- diagonal
-- a rigid variable might not be less than it self, so no -.. on the
-- rigid part of the diagonal
         solvable = all (\ x -> x >= Finite 0) [ m!(i,i) | i <- rInds ] && True

{-  Andreas, 2012-09-19
    We now can have constraints between rigid variables, like i < j.
    Thus we skip the following two test.  However, a solution must be
    checked for consistency with the constraints on rigid vars.

-- a rigid variable might not be bounded below by infinity or
-- bounded above by a constant
-- it might not be related to another rigid variable
           all (\ (r,  r') -> r == r' ||
                let Just row = (Map.lookup (Rigid r)  (nodeMap gr))
                    Just col = (Map.lookup (Rigid r') (nodeMap gr))
                    edge = m!(row,col)
                in  isBelow r edge r' )
             [ (r,r') | r <- rigids, r' <- rigids ]
           &&
-- a flexible variable might not be strictly below a rigid variable
           all (\ (x, v) ->
                let Just row = (Map.lookup (Flex x)  (nodeMap gr))
                    Just col = (Map.lookup (Rigid (RVar v)) (nodeMap gr))
                    edge = m!(row,col)
                in  edge >= Finite 0)
             [ (x,v) | x <- flexs, (RVar v) <- rigids ]
-}

         inScope :: FlexId -> Rigid -> Bool
         inScope x (RConst _) = True
         inScope x (RVar v)   = scope v
             where Just scope = Map.lookup x (flexScope gr)

{- loop1

while flexible variables and rigid rows left
  find a rigid variable row i
    for all flexible columns j
      if i --n--> j with n<=0 (meaning i + n <= j) then j = i + n

-}
         loop1 :: [FlexId] -> [Rigid] -> Solution -> Maybe Solution
         loop1 [] rgds subst = Just subst
         loop1 flxs [] subst = loop2 flxs subst
         loop1 flxs (r:rgds) subst =
            let row = fromJust $ Map.lookup (Rigid r) (nodeMap gr)
                (flxs',subst') =
                  foldl' (\ (flx,sub) f ->
                          let col = fromJust $ Map.lookup (Flex f) (nodeMap gr)
                          in  case (inScope f r, m!(row,col)) of
--                                Finite z | z <= 0 ->
                                (True, Finite z) ->
                                   let trunc z | z >= 0 = 0
                                            | otherwise = -z
                                   in (flx, extendSolution sub f (sizeRigid r (trunc z)))
                                _ -> (f : flx, sub)
                     ) ([], subst) flxs
            in loop1 flxs' rgds subst'

{- loop2

while flexible variables j left
  search the row j for entry i
    if j --n--> i with n >= 0 (meaning j <= i + n) then j = i

-}
         loop2 :: [FlexId] -> Solution -> Maybe Solution
         loop2 [] subst = Just subst
         loop2 (f:flxs) subst = loop3 0 subst
           where row = fromJust $ Map.lookup (Flex f) (nodeMap gr)
                 loop3 col subst | col >= n =
                   -- default to infinity
                    loop2 flxs (extendSolution subst f (SizeConst Infinite))
                 loop3 col subst =
                   case Map.lookup col (intMap gr) of
                     Just (Rigid r) | not (infinite r) ->
                       case (inScope f r, m!(row,col)) of
                        (True, Finite z) | z >= 0 ->
                            loop2 flxs (extendSolution subst f (sizeRigid r z))
                        (_, Infinite) -> loop3 (col+1) subst
                        _ -> -- trace ("unusable rigid: " ++ show r ++ " for flex " ++ show f)
                              Nothing  -- NOT: loop3 (col+1) subst
                     _ -> loop3 (col+1) subst



-- Testing ----------------------------------------------------------------

genGraph :: Ord node => Float -> Gen edge -> [node] -> Gen (AdjList node edge)
genGraph density edge nodes = do
  Map.fromList . concat <$> mapM neighbours nodes
  where
    k = round (100 * density)
    neighbours n = do
      ns <- concat <$> mapM neighbour nodes
      case ns of
        []  -> elements [[(n, [])], []]
        _   -> return [(n, ns)]
    neighbour n = frequency
      [ (k, do e <- edge
               ns <- neighbour n
               return ((n, e):ns))
      , (100 - k, return [])
      ]

newtype Distance = Dist Nat
  deriving (Eq, Ord, Num, Integral, Show, Enum, Real)

instance SemiRing Distance where
  oplus  (Dist a) (Dist b) = Dist (min a b)
  otimes (Dist a) (Dist b) = Dist (a + b)

genGraph_ :: Nat -> Gen (AdjList Nat Distance)
genGraph_ n =
  genGraph 0.2 (Dist <$> natural) [0..n - 1]

lookupEdge :: Ord n => n -> n -> AdjList n e -> Maybe e
lookupEdge i j g = lookup j =<< Map.lookup i g

edges :: Ord n => AdjList n e -> [(n,n,e)]
edges g = do
  (i, ns) <- Map.toList g
  (j, e)  <- ns
  return (i, j, e)

-- | Check that no edges get longer when completing a graph.
prop_smaller n' =
  forAll (genGraph_ n) $ \g ->
  let g' = warshallG g in
  and [ lookupEdge i j g' =< e
      | (i, j, e) <- edges g
      ]
  where
    n = abs (div n' 2)
    Nothing =< _ = False
    Just x  =< y = x <= y

newEdge i j e = Map.insertWith (++) i [(j, e)]

genPath :: Nat -> Nat -> Nat -> AdjList Nat Distance -> Gen (AdjList Nat Distance)
genPath n i j g = do
  es <- listOf $ (,) <$> node <*> edge
  v  <- edge
  return $ addPath i (es ++ [(j, v)]) g
  where
    edge = Dist <$> natural
    node = choose (0, n - 1)
    addPath _ [] g = g
    addPath i ((j, v):es) g =
      newEdge i j v $ addPath j es g

-- | Check that all transitive edges are added.
prop_path n' =
  forAll (genGraph_ n) $ \g ->
  forAll (two $ choose (0, n - 1)) $ \(i, j) ->
  forAll (genPath n i j g) $ \g' ->
  isJust (lookupEdge i j $ warshallG g')
  where
    n = abs (div n' 2) + 1

mapNodes :: (Ord node, Ord node') => (node -> node') -> AdjList node edge -> AdjList node' edge
mapNodes f = Map.map f' . Map.mapKeys f
  where
    f' es = [ (f n, e) | (n,e) <- es ]

-- | Check that no edges are added between components.
prop_disjoint n' =
  forAll (two $ genGraph_ n) $ \(g1, g2) ->
  let g  = Map.union (mapNodes Left g1) (mapNodes Right g2)
      g' = warshallG g
  in all disjoint (Map.assocs g')
  where
    n = abs (div n' 3)
    disjoint (Left i, es)  = all (isLeft . fst) es
    disjoint (Right i, es) = all (isRight . fst) es
    isLeft = either (const True) (const False)
    isRight = not . isLeft

prop_stable n' =
  forAll (genGraph_ n) $ \g ->
  let g' = warshallG g in
  g' =~= warshallG g'
  where
    n = abs (div n' 2)
    g =~= g' = sort (edges g) == sort (edges g')

tests :: IO Bool
tests = runTests "Agda.Utils.Warshall" []
