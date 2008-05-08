------------------------------------------------------------------------
-- Precedence graphs
------------------------------------------------------------------------

module PrecedenceGraph
    -- * Precedence graphs
  ( Name
  , Assoc(..)
  , Fixity(..)
  , Node
  , PrecedenceGraph
    -- * Constructing precedence graphs
  , empty
  , bindsAs
  , bindsBetween
  , unrelated
    -- * Inspecting precedence graphs
  , successors
  , annotation
  , nodes
  , allOperators
  , allInfix
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive ((&))
import Utilities

------------------------------------------------------------------------
-- Types

-- | A name is a /non-empty/ list of /non-empty/ name parts.

type Name = [String]

-- | Associativity.

data Assoc = Non | L | R
             deriving (Eq, Ord, Show)

-- | Fixity.

data Fixity = Prefix | Postfix | Infix Assoc
              deriving (Eq, Ord, Show)

-- | Precedence graph node labels.

type Node = Int

-- | Precedence graphs.

-- Invariant: Has to be acyclic.

newtype PrecedenceGraph =
  PG { unPG :: G.Gr (Map Fixity (Set Name)) () }
     deriving Show

------------------------------------------------------------------------
-- Inspecting precedence graphs

-- | The successors of a node.

successors :: PrecedenceGraph -> Node -> Set Node
successors g n = Set.fromList $ G.suc (unPG g) n

-- | A node's annotation.

annotation :: PrecedenceGraph -> Node -> Map Fixity (Set Name)
annotation g n = case G.lab (unPG g) n of
  Nothing  -> Map.empty
  Just ann -> ann

-- | The nodes in the graph.

nodes :: PrecedenceGraph -> Set Node
nodes = Set.fromList . G.nodes . unPG

-- | All operators in the graph.

allOperators :: PrecedenceGraph -> Map Fixity (Set Name)
allOperators g =
  Map.unionsWith (Set.union) $
    map' (annotation g) (nodes g)

-- | All infix operators in the range of the map.

allInfix :: Map Fixity (Set Name) -> Set Name
allInfix m = Set.unions [m ! Infix p | p <- [Non, L, R]]

-- | Is the graph acyclic?

-- Check this by ensuring that the graph is simple (no loops) and all
-- strongly connected components have size 1.

acyclic :: PrecedenceGraph -> Bool
acyclic (PG g) = G.isSimple g && all (\c -> length c == 1) (G.scc g)

------------------------------------------------------------------------
-- Constructing precedence graphs

-- An empty precedence graph.

empty :: PrecedenceGraph
empty = PG G.empty

-- @bindsAs op fix n g@ adds @op@ (with fixity @fix@) to node @n@.
-- 
-- Precondition: @n@ has to exist in @g@, and @n@ should not already
-- be annotated with @op@. (The second precondition is not checked.)

bindsAs :: Name -> Fixity -> Node -> PrecedenceGraph -> PrecedenceGraph
bindsAs op fix n (PG g) = case G.match n g of
  (Nothing, g') -> error "bindsAs: The node does not exist."
  (Just (pre, n, a, suc), g') ->
    PG ((pre, n, Map.adjust (Set.insert op) fix a, suc) & g')

-- @bindsBetween op fix tighterThan looserThan n g@ adds a new node to
-- @g@, annotated with @op@ (with fixity @fix@). Edges are added from
-- all nodes in @tighterThan@, and their predecessors. Edges are also
-- added to all nodes in @looserThan@, and their successors. The new
-- node label is returned along with the new graph.
--
-- Precondition: The resulting graph has to be acyclic.

bindsBetween :: Name -> Fixity -> [Node] -> [Node] ->
                PrecedenceGraph -> (Node, PrecedenceGraph)
bindsBetween op fixity tighterThan looserThan (PG g)
  | acyclic g' = (new, g')
  | otherwise  = error "bindsBetween: Cyclic result."
  where
  [new]          = G.newNodes 1 g
  allLooserThan  = looserThan  : map (G.suc g) looserThan
  allTighterThan = tighterThan : map (G.pre g) tighterThan
  fix            = map ((,) ()) . efficientNub . concat
  ctxt           = ( fix allTighterThan
                   , new
                   , Map.singleton fixity (Set.singleton op)
                   , fix allLooserThan
                   )
  g'             = PG (ctxt & g)

-- @unrelated op fix g@ add a fresh node to @g@, annotated with @op@
-- (with fixity @fix@). No new edges are added.

unrelated :: Name -> Fixity -> PrecedenceGraph ->
             (Node, PrecedenceGraph)
unrelated op fix = bindsBetween op fix [] []
