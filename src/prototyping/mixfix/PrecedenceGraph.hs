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
    -- * Tests
  , tests
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Arrow
import Control.Monad
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive ((&))
import Data.Function
import qualified Data.List as List
import Test.QuickCheck

import Utilities hiding (tests)

------------------------------------------------------------------------
-- Types

-- | A name is a /non-empty/ list of /non-empty/ name parts.

newtype Name = Name [String]
               deriving (Eq, Ord, Show)

-- | The name invariant.

nameInvariant (Name ns) = nonEmpty ns && all nonEmpty ns
  where nonEmpty = not . null

-- | Associativity.

data Assoc = Non | L | R
             deriving (Eq, Ord, Show)

-- | Fixity.

data Fixity = Prefix | Postfix | Infix Assoc
              deriving (Eq, Ord, Show)

-- | Precedence graph node labels.

type Node = Int

-- | Precedence graphs.

newtype PrecedenceGraph =
  PG { unPG :: G.Gr (Map Fixity (Set Name)) () }
     deriving Show

-- | Graph invariant: Has to be an acyclic graph (not a multi-graph).

graphInvariant :: PrecedenceGraph -> Bool
graphInvariant (PG g) = acyclic g && graph g

------------------------------------------------------------------------
-- Inspecting precedence graphs

-- | Is the graph empty?

isEmpty :: PrecedenceGraph -> Bool
isEmpty (PG g) = G.isEmpty g

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

------------------------------------------------------------------------
-- Constructing precedence graphs

-- An empty precedence graph.

empty :: PrecedenceGraph
empty = PG G.empty

prop_empty = graphInvariant empty

-- @bindsAs op fix n g@ adds @op@ (with fixity @fix@) to node @n@.
-- 
-- Precondition: @n@ has to exist in @g@.

bindsAs :: Name -> Fixity -> Node -> PrecedenceGraph -> PrecedenceGraph
bindsAs op fix n (PG g) = case G.match n g of
  (Nothing, g') -> error "bindsAs: The node does not exist."
  (Just (pre, n, a, suc), g') ->
    PG ((pre, n, Map.adjust (Set.insert op) fix a, suc) & g')

prop_bindsAs op fix g =
  not (isEmpty g) ==>
  forAll (nodeIn g) $ \n ->
    graphInvariant (bindsAs op fix n g)

-- @bindsBetween op fix tighterThan looserThan g@ adds a new node to
-- @g@, annotated with @op@ (with fixity @fix@). Edges are added from
-- all nodes in @tighterThan@, and their predecessors. Edges are also
-- added to all nodes in @looserThan@, and their successors. The new
-- node label is returned along with the new graph.
--
-- Precondition: The resulting graph has to be acyclic.

bindsBetween :: Name -> Fixity -> [Node] -> [Node] ->
                PrecedenceGraph -> (Node, PrecedenceGraph)
bindsBetween op fixity tighterThan looserThan (PG g)
  | acyclic g' = (new, PG g')
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
  g'             = ctxt & g

-- Note that the distribution of random values used to test this
-- function is not uniform.

prop_bindsBetween op fixity g =
  forAll (nodesIn g) $ \tighterThan ->
  forAll (nodesNotBelow tighterThan g) $ \looserThan ->
    graphInvariant (snd $ bindsBetween op fixity tighterThan looserThan g)

-- @unrelated op fix g@ add a fresh node to @g@, annotated with @op@
-- (with fixity @fix@). No new edges are added.

unrelated :: Name -> Fixity -> PrecedenceGraph ->
             (Node, PrecedenceGraph)
unrelated op fix = bindsBetween op fix [] []

------------------------------------------------------------------------
-- Generators and other test helpers

instance Arbitrary Name where
  arbitrary = liftM Name $ listOf1 (listOf1 (elements "abcd"))

  shrink (Name ns) = filter nameInvariant $ map Name $ shrink ns

instance Arbitrary Assoc where
  arbitrary = elements [Non, L, R]

instance Arbitrary Fixity where
  arbitrary = frequency [ (2, elements [Prefix, Postfix])
                        , (3, liftM Infix arbitrary)
                        ]

mapOfSetsToList   = Map.fromList . map (id *** Set.fromList)
mapOfSetsFromList = map (id *** Set.toList) . Map.toList

instance Arbitrary PrecedenceGraph where
  arbitrary = liftM PG (acyclicGraph node arbitrary)
    where node = liftM mapOfSetsToList arbitrary

  shrink = map PG .
           map (G.nmap mapOfSetsToList) .
           take 500 . shrinkGraph .
           G.nmap mapOfSetsFromList .
           unPG

-- | Generates a node from the graph.
--
-- Precondition: Non-empty graph.

nodeIn :: PrecedenceGraph -> Gen Node
nodeIn = elements . Set.toList . nodes

-- | Generates a list of (distinct) nodes from the graph.

nodesIn :: PrecedenceGraph -> Gen [Node]
nodesIn = sublist . Set.toList . nodes

prop_nodesIn g = forAll (nodesIn g) distinct

-- | @nodesNotBelow ns g@ generates a list of nodes from @g@. These
-- nodes must not be \"below\" those in @ns@, i.e. they may not be
-- predecessors of any node from @ns@ in the transitive closure of
-- @g@.

nodesNotBelow :: [Node] -> PrecedenceGraph -> Gen [Node]
nodesNotBelow ns g = sublist notBelow
  where
  notBelow     = filter (not . isBelow ns) (G.nodes $ unPG g)
  isBelow ns   = \x -> any (\n -> n `elem` G.suc transClosure x) ns
  transClosure = G.trc (unPG g)

-- | All tests.

tests = do
  quickCheck nameInvariant
  quickCheck (all nameInvariant . shrink)
  quickCheck graphInvariant
  quickCheck (all graphInvariant . shrink)
  quickCheck prop_nodesIn
  quickCheck prop_empty
  quickCheck prop_bindsAs
  quickCheck prop_bindsBetween
