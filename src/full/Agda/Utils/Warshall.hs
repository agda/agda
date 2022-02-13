
{- | Construct a graph from constraints
@
   x + n <= y   becomes   x ---(-n)---> y
   x <= n + y   becomes   x ---(+n)---> y
@
the default edge (= no edge) is labelled with infinity.

Building the graph involves keeping track of the node names.
We do this in a finite map, assigning consecutive numbers to nodes.
-}
module Agda.Utils.Warshall where

import Control.Monad.State

import Data.Maybe
import Data.Array
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Utils.SemiRing
import Agda.Utils.List (nubOn)
import Agda.Utils.Pretty as P

import Agda.Utils.Impossible

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

type AdjList node edge = Map node [(node, edge)]

-- | Warshall's algorithm on a graph represented as an adjacency list.
warshallG :: (SemiRing edge, Ord node) => AdjList node edge -> AdjList node edge
warshallG g = fromMatrix $ warshall m
  where
    nodes = zip (nubOn id $ Map.keys g ++ map fst (concat $ Map.elems g))
                [0..]
    len   = length nodes
    b     = ((0,0), (len - 1,len - 1))

    edge i j = do
      es <- Map.lookup i g
      foldr oplus Nothing [ Just v | (j', v) <- es, j == j' ]

    m = array b [ ((n, m), edge i j) | (i, n) <- nodes, (j, m) <- nodes ]

    fromMatrix matrix = Map.fromListWith __IMPOSSIBLE__ $ do
      (i, n) <- nodes
      let es = [ (fst (nodes !! m), e)
               | m <- [0..len - 1]
               , Just e <- [matrix ! (n, m)]
               ]
      return (i, es)

-- | Edge weight in the graph, forming a semi ring.
data Weight
  = Finite Int
  | Infinite
  deriving (Eq, Show)

inc :: Weight -> Int -> Weight
inc Infinite   n = Infinite
inc (Finite k) n = Finite (k + n)

instance Pretty Weight where
  pretty (Finite i) = pretty i
  pretty Infinite   = "."

instance Ord Weight where
  a <= Infinite = True
  Infinite <= b = False
  Finite a <= Finite b = a <= b

instance SemiRing Weight where
  ozero = Infinite
  oone  = Finite 0

  oplus = min

  otimes Infinite _ = Infinite
  otimes _ Infinite = Infinite
  otimes (Finite a) (Finite b) = Finite (a + b)

-- constraints ---------------------------------------------------

-- | Nodes of the graph are either
-- - flexible variables (with identifiers drawn from @Int@),
-- - rigid variables (also identified by @Int@s), or
-- - constants (like 0, infinity, or anything between).

data Node = Rigid Rigid
          | Flex  FlexId
            deriving (Eq, Ord)

data Rigid = RConst Weight
           | RVar RigidId
             deriving (Eq, Ord)

type NodeId  = Int
type RigidId = Int
type FlexId  = Int
type Scope   = RigidId -> Bool
-- ^ Which rigid variables a flex may be instatiated to.

instance Pretty Node where
  pretty (Flex  i)                   = "?" P.<> pretty i
  pretty (Rigid (RVar i))            = "v" P.<> pretty i
  pretty (Rigid (RConst Infinite))   = "#"
  pretty (Rigid (RConst (Finite n))) = pretty n

infinite :: Rigid -> Bool
infinite (RConst Infinite) = True
infinite _                 = False

-- | @isBelow r w r'@
--   checks, if @r@ and @r'@ are connected by @w@ (meaning @w@ not infinite),
--   whether @r + w <= r'@.
--   Precondition: not the same rigid variable.
isBelow :: Rigid -> Weight -> Rigid -> Bool
isBelow _ Infinite _ = True
isBelow _ n (RConst Infinite) = True
isBelow (RConst (Finite i)) (Finite n) (RConst (Finite j)) = i + n <= j
isBelow _ _ _ = False -- rigid variables are not related

-- | A constraint is an edge in the graph.
data Constraint
  = NewFlex FlexId Scope
  | Arc Node Int Node
    -- ^ For @Arc v1 k v2@  at least one of @v1@ or @v2@ is a @MetaV@ (Flex),
    --                      the other a @MetaV@ or a @Var@ (Rigid).
    --   If @k <= 0@ this means  @suc^(-k) v1 <= v2@
    --   otherwise               @v1 <= suc^k v3@.

instance Pretty Constraint where
  pretty (NewFlex i s) = hcat [ "SizeMeta(?", pretty i, ")" ]
  pretty (Arc v1 k v2)
    | k == 0    = hcat [ pretty v1, "<=", pretty v2 ]
    | k < 0     = hcat [ pretty v1, "+", pretty (-k), "<=", pretty v2 ]
    | otherwise = hcat [ pretty v1, "<=", pretty v2, "+", pretty k ]

type Constraints = [Constraint]

emptyConstraints :: Constraints
emptyConstraints = []

-- graph (matrix) ------------------------------------------------

data Graph = Graph
  { flexScope :: Map FlexId Scope           -- ^ Scope for each flexible var.
  , nodeMap   :: Map Node NodeId            -- ^ Node labels to node numbers.
  , intMap    :: Map NodeId Node            -- ^ Node numbers to node labels.
  , nextNode  :: NodeId                     -- ^ Number of nodes @n@.
  , graph     :: NodeId -> NodeId -> Weight -- ^ The edges (restrict to @[0..n[@).
  }

-- | The empty graph: no nodes, edges are all undefined (infinity weight).
initGraph :: Graph
initGraph = Graph Map.empty Map.empty Map.empty 0 (\ x y -> Infinite)

-- | The Graph Monad, for constructing a graph iteratively.
type GM = State Graph

-- | Add a size meta node.
addFlex :: FlexId -> Scope -> GM ()
addFlex x scope = do
  modify $ \ st -> st { flexScope = Map.insert x scope (flexScope st) }
  _ <- addNode (Flex x)
  return ()

-- | Lookup identifier of a node.
--   If not present, it is added first.
addNode :: Node -> GM Int
addNode n = do
  st <- get
  case Map.lookup n (nodeMap st) of
    Just i -> return i
    Nothing -> do
      let i = nextNode st
      put $ st { nodeMap  = Map.insert n i (nodeMap st)
               , intMap   = Map.insert i n (intMap st)
               , nextNode = i + 1
               }
      return i

-- | @addEdge n1 k n2@
--   improves the weight of egde @n1->n2@ to be at most @k@.
--   Also adds nodes if not yet present.
addEdge :: Node -> Int -> Node -> GM ()
addEdge n1 k n2 = do
  i1 <- addNode n1
  i2 <- addNode n2
  st <- get
  let graph' x y = if (x,y) == (i1,i2) then Finite k `oplus` graph st x y
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

-- | A matrix with row descriptions in @b@ and column descriptions in @c@.
data LegendMatrix a b c = LegendMatrix
  { matrix   :: Matrix a
  , rowdescr :: Int -> b
  , coldescr :: Int -> c
  }

instance (Pretty a, Pretty b, Pretty c) => Pretty (LegendMatrix a b c) where
  pretty (LegendMatrix m rd cd) =
    -- first show column description
    let ((r,c),(r',c')) = bounds m
    in foldr (\ j s -> "\t" P.<> pretty (cd j) P.<> s) "" [c .. c'] P.<>
    -- then output rows
       foldr (\ i s -> "\n" P.<> pretty (rd i) P.<>
                foldr (\ j t -> "\t" P.<> pretty (m!(i,j)) P.<> t)
                      s
                      [c .. c'])
             "" [r .. r']

-- solving the constraints -------------------------------------------

-- | A solution assigns to each flexible variable a size expression
--   which is either a constant or a @v + n@ for a rigid variable @v@.
type Solution = Map Int SizeExpr

emptySolution :: Solution
emptySolution = Map.empty

extendSolution :: Solution -> Int -> SizeExpr -> Solution
extendSolution subst k v = Map.insert k v subst

data SizeExpr = SizeVar RigidId Int   -- ^ e.g. x + 5
              | SizeConst Weight      -- ^ a number or infinity

instance Pretty SizeExpr where
  pretty (SizeVar n 0) = pretty (Rigid (RVar n))
  pretty (SizeVar n k) = pretty (Rigid (RVar n)) P.<> "+" P.<> pretty k
  pretty (SizeConst w) = pretty w

-- | @sizeRigid r n@ returns the size expression corresponding to @r + n@
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

{- compute solution

a solution CANNOT exist if

  v < v  for a rigid variable v

  -- Andreas, 2012-09-19 OUTDATED are:

  -- v <= v' for rigid variables v,v'

  -- x < v   for a flexible variable x and a rigid variable v


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
solve cs = -- trace (prettyShow cs) $
   -- trace (prettyShow lm0) $
    -- trace (prettyShow lm) $ -- trace (prettyShow d) $
     let solution = if solvable then loop1 flexs rigids emptySolution
                    else Nothing
     in -- trace (prettyShow solution) $
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
         flexs  = List.foldl' (\ l -> \case (Flex i ) -> i : l
                                            (Rigid _) -> l)     [] ns
         -- a set of rigid variables
         rigids = List.foldl' (\ l -> \case (Flex _ ) -> l
                                            (Rigid i) -> i : l) [] ns

         -- rigid matrix indices
         rInds = List.foldl' (\ l r -> let Just i = Map.lookup (Rigid r) (nodeMap gr)
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
                  List.foldl' (\ (flx,sub) f ->
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
                        _ -> -- trace ("unusable rigid: " ++ prettyShow r ++ " for flex " ++ prettyShow f)
                              Nothing  -- NOT: loop3 (col+1) subst
                     _ -> loop3 (col+1) subst
