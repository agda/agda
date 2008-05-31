------------------------------------------------------------------------
-- Precedence graphs
------------------------------------------------------------------------

{-# LANGUAGE PatternSignatures #-}

module PrecedenceGraph
    -- * Precedence graphs
  ( Assoc(..)
  , Fixity(..)
  , Name(..)
  , Node
  , PrecedenceGraph
    -- * Constructing precedence graphs
  , empty
  , bindsAs
  , bindsBetween
  , unrelated
    -- * Inspecting precedence graphs
  , isEmpty
  , containedIn
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
import qualified Data.List  as List
import qualified Data.Maybe as Maybe
import Test.QuickCheck

import Utilities hiding (tests)

------------------------------------------------------------------------
-- Types

-- | Associativity.

data Assoc = Non | L | R
             deriving (Eq, Ord, Show)

-- | Fixity.

data Fixity = Prefix | Postfix | Infix Assoc
              deriving (Eq, Ord, Show)

-- | A name is a completely qualified name.

data Name = Name { moduleName :: [String]
                 , fixity     :: Maybe Fixity
                   -- ^ 'Just' something for operators.
                 , nameParts  :: [String]
                   -- ^ A /non-empty/ list of /non-empty/ name parts.
                   -- A singleton list for non-operators.
                 }
            deriving (Show)

isOperator :: Name -> Bool
isOperator = Maybe.isJust . fixity

-- | The associativity of a name should be uniquely determined by the
-- other components, so equality and ordering does not make use of the
-- associativity.

relevant (Name m f n) = (m, dropAssoc f, n)
  where
  dropAssoc Nothing          = 0
  dropAssoc (Just Prefix)    = 1
  dropAssoc (Just Postfix)   = 2
  dropAssoc (Just (Infix _)) = 3

instance Eq Name where
  (==) = (==) `on` relevant

instance Ord Name where
  compare = compare `on` relevant

-- | The name invariant.

nameInvariant n@(Name m f ns) =
  nonEmpty ns && all nonEmpty ns &&
  if isOperator n then True else length ns == 1
  where nonEmpty = not . null

-- | Precedence graph node labels.

type Node = Int

-- | Node contents.

type NodeContents = Map Fixity (Set Name)

-- | Precedence graphs.

data PrecedenceGraph =
  PG { precGraph :: G.Gr NodeContents ()
     , nameMap   :: Map Name Node
       -- ^ This should be a trie.
     }
     deriving Show

-- | All names from the node.

nodeNames :: NodeContents -> [Name]
nodeNames = concatMap Set.elems . Map.elems

-- | The name map can be calculated from the precedence graph. (This
-- function is only used by the testing code.)
--
-- Precondition: Every unique name must occur at most once.

calculatedNameMap :: G.Gr (Map Fixity (Set Name)) () ->
                     Map Name Node
calculatedNameMap g
  | distinct (map fst nns) = Map.fromList nns
  | otherwise              =
      error "calculatedNameMap: Duplicated names."
  where
  nns = concatMap (\(node, ns) -> map (\n -> (n, node)) ns) $
        map (id *** nodeNames) $
        G.labNodes g

-- | The graph has to be an acyclic graph (not a multi-graph), the
-- name map should be consistent, the fixity maps have to be
-- consistent, and all nodes and fixity maps have to be non-empty.

graphInvariant :: PrecedenceGraph -> Bool
graphInvariant pg@(PG g m) =
  acyclic g && graph g && m == calculatedNameMap g && 
  all (\(f, s) -> all (== Just f) $ map' fixity s)
      (Map.toList $ allOperators pg) &&
  all (not . Map.null) maps &&
  all (all (not . Set.null)) (map Map.elems maps)
  where
  maps     = map' (annotation pg) $ nodes pg
  nonEmpty = not . null

------------------------------------------------------------------------
-- Inspecting precedence graphs

-- | The node corresponding to a given name, if any.

lookupNode :: PrecedenceGraph -> Name -> Maybe Node
lookupNode pg op = Map.lookup op (nameMap pg)

-- | Is the given name in the graph?

containedIn :: Name -> PrecedenceGraph -> Bool
n `containedIn` pg = Maybe.isJust $ lookupNode pg n

-- | Is the graph empty?

isEmpty :: PrecedenceGraph -> Bool
isEmpty = G.isEmpty . precGraph

-- | The successors of a node.

successors :: PrecedenceGraph -> Node -> Set Node
successors pg n = Set.fromList $ G.suc (precGraph pg) n

-- | A node's annotation.

annotation :: PrecedenceGraph -> Node -> Map Fixity (Set Name)
annotation pg n = case G.lab (precGraph pg) n of
  Nothing  -> Map.empty
  Just ann -> ann

-- | The nodes in the graph.

nodes :: PrecedenceGraph -> Set Node
nodes = Set.fromList . G.nodes . precGraph

-- | All operators in the graph.

allOperators :: PrecedenceGraph -> Map Fixity (Set Name)
allOperators pg =
  Map.unionsWith (Set.union) $
    map' (annotation pg) (nodes pg)

-- | All infix operators in the range of the map.

allInfix :: Map Fixity (Set Name) -> Set Name
allInfix m = Set.unions [m ! Infix p | p <- [Non, L, R]]

------------------------------------------------------------------------
-- Constructing precedence graphs

-- An empty precedence graph.

empty :: PrecedenceGraph
empty = PG G.empty Map.empty

prop_empty = graphInvariant empty

-- @bindsAs op fix n pg@ adds @op@ (with fixity @fix@) to the node
-- corresponding to @n@.
--
-- Precondition: @n@ has to exist in @pg@, @op@ must not exist in
-- @pg@, and @op@ has to be an operator.

bindsAs :: Name -> Name -> PrecedenceGraph -> PrecedenceGraph
bindsAs op asThis pg = case fixity op of
  Nothing -> error "bindsAs: This is not an operator."
  Just f  -> case (Map.lookup asThis (nameMap pg), lookupNode pg op) of
    (Nothing, _) -> error "bindsAs: The node does not exist."
    (_, Just _)  -> error "bindsAs: The name is already in the graph."
    (Just node, _) -> case G.match node (precGraph pg) of
      (Nothing, g') -> error "bindsAs: Internal error."
      (Just (pre, n, a,  suc), g') ->
        PG ((pre, n, a', suc) & g')
           (Map.insert op n (nameMap pg))
        where a' = Map.insertWith Set.union f (Set.singleton op) a

prop_bindsAs pg =
  not (isEmpty pg) ==>
  forAll (operatorNotIn pg) $ \op ->
  forAll (nameIn pg) $ \n ->
    graphInvariant (bindsAs op n pg)

-- @bindsBetween op fix tighterThan looserThan pg@ adds a new node to
-- @pg@, annotated with @op@ (with fixity @fix@). Edges are added from
-- all nodes corresponding to names in @tighterThan@, and to all nodes
-- corresponding to names in @looserThan@.
--
-- Precondition: The resulting graph has to be acyclic, @op@ must be
-- an operator, @op@ must not exist in @pg@, and all the other names
-- in the input have to exist in @pg@.

bindsBetween :: Name -> [Name] -> [Name] ->
                PrecedenceGraph -> PrecedenceGraph
bindsBetween op tighterThan looserThan pg@(PG g _)
  | op `containedIn` pg =
      error "bindsBetween: The name is already in the graph."
  | otherwise = case ( fixity op
                     , targetNodes looserThan
                     , targetNodes tighterThan
                     ) of
      (Just f, Just allLooserThan, Just allTighterThan)
        | acyclic g' -> PG g' (Map.insert op new (nameMap pg))
        | otherwise  -> error "bindsBetween: Cyclic result."
        where
        ctxt = ( fix allTighterThan
               , new
               , Map.singleton f (Set.singleton op)
               , fix allLooserThan
               )
        g'   = ctxt & g
      (Nothing, _, _) -> error "bindsBetween: The name is not an operator."
      _ -> error "bindsBetween: Some name is not present in the graph."
  where
  targetNodes us = mapM (\u -> Map.lookup u (nameMap pg)) us

  fix   = map ((,) ()) . efficientNub
  [new] = G.newNodes 1 g

-- Note that the distribution of random values used to test this
-- function is not uniform.

prop_bindsBetween pg =
  forAll (operatorNotIn pg) $ \op ->
  forAll (namesIn pg) $ \tighterThan ->
  forAll (namesNotBelow tighterThan pg) $ \looserThan ->
    graphInvariant (bindsBetween op tighterThan looserThan pg)

-- @unrelated op fix pg@ add a fresh node to @pg@, annotated with @op@
-- (with fixity @fix@). No new edges are added.

unrelated :: Name -> PrecedenceGraph -> PrecedenceGraph
unrelated op = bindsBetween op [] []

------------------------------------------------------------------------
-- Generators and other test helpers

instance Arbitrary Assoc where
  arbitrary = elements [Non, L, R]

instance Arbitrary Fixity where
  arbitrary = frequency [ (2, elements [Prefix, Postfix])
                        , (3, liftM Infix arbitrary)
                        ]

-- | Generates a name with the given fixity.

name :: Maybe Fixity -> Gen Name
name mfix = do
  liftM3 Name mod (return mfix) $ case mfix of
    Nothing -> op 1
    Just _  -> op 6
  where
  character = elements "abcd"
  mod       = list' (choose (0, 2)) $ list' (choose (0, 2)) character
  op n      = list' (choose (1, n)) $ list' (choose (1, 3)) character

  list' :: Gen Integer -> Gen a -> Gen [a]
  list' = list

-- | Generates an operator.

operator :: Gen Name
operator = name . Just =<< arbitrary

prop_operator =
  forAll operator $ \op ->
    isOperator op

instance Arbitrary Name where
  arbitrary = name =<< arbitrary

  shrink (Name u f op) =
    filter nameInvariant $
    map (\(x, y, z) -> Name x y z) $
    shrink (u, f, op)

instance Arbitrary PrecedenceGraph where
  arbitrary = do
    -- Since names is a set the generated names have to be unique.
    names <- fmap Set.fromList arbitrary
    nodeContents <- partitionsOf $ Set.toList names
    g <- acyclicGraph (Maybe.catMaybes $ map mkNode nodeContents)
                      arbitrary
    return (PG g (calculatedNameMap g))
    where
    mkNode :: [Name] -> Maybe NodeContents
    mkNode = ensureNonEmpty .
             Map.fromListWith Set.union .
             map (\n -> (Maybe.fromJust (fixity n), Set.singleton n)) .
             filter isOperator

    ensureNonEmpty ns =
      case (Map.null ns, any Set.null (Map.elems ns)) of
        (False, False) -> Just ns
        _              -> Nothing

  shrink =
    map (\g -> PG g (calculatedNameMap g)) .
    map (G.nmap mapOfSetsFromList) .
    shrinkGraph .
    G.nmap mapOfSetsToList .
    precGraph
    where
    mapOfSetsFromList = Map.fromList . map (id *** Set.fromList)
    mapOfSetsToList   = map (id *** Set.toList) . Map.toList

-- | Generates an operator which is not contained in the graph.

operatorNotIn :: PrecedenceGraph -> Gen Name
operatorNotIn pg =
  operator `suchThat` \op ->
    not (op `containedIn` pg)

-- | Generates a name contained in the graph.
--
-- Precondition: Non-empty graph.

nameIn :: PrecedenceGraph -> Gen Name
nameIn = elements . Map.keys . nameMap

prop_nameIn pg =
  not (isEmpty pg) ==>
  forAll (nameIn pg) $ \n ->
    n `containedIn` pg

-- | Generates a list of (distinct) names contained in the graph.

namesIn :: PrecedenceGraph -> Gen [Name]
namesIn = sublist . Map.keys . nameMap

prop_namesIn pg =
  forAll (namesIn pg) $ \ns ->
    all (`containedIn` pg) ns

-- | @namesNotBelow ns pg@ generates a list of names from @pg@. These
-- names must correspond to nodes which are not \"below\" those in
-- @ns@, i.e. they may not correspond to predecessors of any node from
-- @ns@ in the transitive closure of @pg@.

namesNotBelow :: [Name] -> PrecedenceGraph -> Gen [Name]
namesNotBelow us pg@(PG g m) = sublist namesNotBelow
  where
  namesNotBelow = concatMap (nodeNames . annotation pg) notBelow
  notBelow      = filter (not . isBelow ns) (G.nodes g)
  ns            = Maybe.catMaybes $ map (\u -> Map.lookup u m) us
  isBelow ns    = \x -> any (\n -> n `elem` G.suc transClosure x) ns
  transClosure  = G.trc g

-- | All tests.

tests = do
  quickCheck nameInvariant
  quickCheck (all nameInvariant . shrink)
  quickCheck prop_operator
  quickCheck graphInvariant
  quickCheck (all graphInvariant . takeSome . shrink)
  quickCheck prop_nameIn
  quickCheck prop_namesIn
  quickCheck prop_empty
  quickCheck prop_bindsAs
  quickCheck prop_bindsBetween
  where
  takeSome xs = take 10 xs ++ take 10 (drop 200 xs)
