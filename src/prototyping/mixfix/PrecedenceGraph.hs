------------------------------------------------------------------------
-- Precedence graphs
------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module PrecedenceGraph
    -- * Precedence graphs
  ( Node
  , Annotation
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
    -- * Tests
  , tests
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Foldable as F
import Control.Arrow
import Control.Monad
import Control.Applicative hiding (empty)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive ((&))
import Data.Function
import qualified Data.List  as List
import qualified Data.Maybe as Maybe
import Test.QuickCheck

import Name      hiding (tests)
import Utilities hiding (tests)

------------------------------------------------------------------------
-- Types

-- | Precedence graph node labels.

type Node = Int

-- | Node annotations. The associativity should be 'Non' for non-infix
-- operators.

type Annotation = Map (Fixity, Assoc) (Set Name)

annotationInvariant ann =
  all (\(fa, s) -> F.all (\n -> fixity n == Just (fst fa)) s
                     &&
                   fixAssocInvariant fa)
      (Map.toList ann) &&
  not (Map.null ann) &&
  not (F.any Set.null ann)

-- | Precedence graphs.

data PrecedenceGraph =
  PG { precGraph :: G.Gr Annotation ()
     , nameMap   :: Map Name Node
     }
     deriving Show

-- | All names from the node.

nodeNames :: Annotation -> [Name]
nodeNames = concatMap Set.elems . Map.elems

-- | The name map can be calculated from the precedence graph. (This
-- function is only used by the testing code.)
--
-- Precondition: Every unique name must occur at most once.

calculatedNameMap :: G.Gr Annotation () -> Map Name Node
calculatedNameMap g
  | distinct (map fst nns) = Map.fromList nns
  | otherwise              =
      error "calculatedNameMap: Duplicated names."
  where
  nns = concatMap (\(node, ns) -> map (\n -> (n, node)) ns) $
        map (id *** nodeNames) $
        G.labNodes g

-- | The graph has to be a graph (not a multi-graph), the name map
-- should be consistent, and the annotations have to be consistent.

graphInvariant :: PrecedenceGraph -> Bool
graphInvariant pg@(PG g m) =
  graph g &&
  m == calculatedNameMap g &&
  all nameInvariant (Map.keys m) &&
  F.all (annotationInvariant . annotation pg) (nodes pg)

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

-- | The predecessors of a node.

predecessors :: PrecedenceGraph -> Node -> Set Node
predecessors pg n = Set.fromList $ G.pre (precGraph pg) n

-- | A node's annotation.

annotation :: PrecedenceGraph -> Node -> Annotation
annotation pg n = case G.lab (precGraph pg) n of
  Nothing  -> Map.empty
  Just ann -> ann

-- | The associativity corresponding to a given name, if any. (This is
-- a potentially inefficient function.)

associativity :: PrecedenceGraph -> Name -> Maybe Assoc
associativity pg n = do
  node <- lookupNode pg n
  return $
    head $
    map (snd . fst) $
    filter snd $
    map (id *** (n `Set.member`)) $
    Map.toList $
    annotation pg node

-- | The nodes in the graph.

nodes :: PrecedenceGraph -> Set Node
nodes = Set.fromList . G.nodes . precGraph

-- | All operators in the graph.

allOperators :: PrecedenceGraph -> Annotation
allOperators pg =
  Map.unionsWith Set.union $
    map (annotation pg) $ Set.toList (nodes pg)

------------------------------------------------------------------------
-- Constructing precedence graphs

-- An empty precedence graph.

empty :: PrecedenceGraph
empty = PG G.empty Map.empty

prop_empty =
  graphInvariant empty &&
  isEmpty empty

-- @bindsAs op ass n pg@ adds @op@ (with associativity @ass@) to the
-- node corresponding to @n@. (The associativity is ignored in the
-- case of pre- and postfix operators.)
--
-- Precondition: @n@ has to exist in @pg@, @op@ must not exist in
-- @pg@, and @op@ has to be an operator.

bindsAs :: Name -> Assoc -> Name -> PrecedenceGraph -> PrecedenceGraph
bindsAs op ass asThis pg = case fixity op of
  Nothing -> error "bindsAs: This is not an operator."
  Just f  -> case (Map.lookup asThis (nameMap pg), lookupNode pg op) of
    (Nothing, _) -> error "bindsAs: The node does not exist."
    (_, Just _)  -> error "bindsAs: The name is already in the graph."
    (Just node, _) -> case G.match node (precGraph pg) of
      (Nothing, g') -> error "bindsAs: Internal error."
      (Just (pre, n, a,  suc), g') ->
        PG ((pre, n, a', suc) & g')
           (Map.insert op n (nameMap pg))
        where a' = Map.insertWith Set.union
                     (ignoreAssoc f ass) (Set.singleton op) a

-- | @associativityCorrect pg op ass@ checks that the associativity of
-- @op@ in @pg@ corresponds to @ass@ (modulo @ignoreAssoc@).

associativityCorrect pg op ass = case fixity op of
  Nothing  -> False
  Just fix -> associativity pg op == Just (snd $ ignoreAssoc fix ass)

prop_bindsAs pg ass =
  not (isEmpty pg) ==>
  forAll (operatorNotIn pg) $ \op ->
  forAll (nameIn pg) $ \n ->
    let pg' = bindsAs op ass n pg in
    graphInvariant pg' &&
    op `containedIn` pg' &&
    lookupNode pg' op == lookupNode pg' n &&
    associativityCorrect pg' op ass

-- @bindsBetween op ass tighterThan looserThan pg@ adds a new node to
-- @pg@, annotated with @op@ (with associativity @ass@, ignored for
-- non-infix operators). Edges are added from all nodes corresponding
-- to names in @tighterThan@, and to all nodes corresponding to names
-- in @looserThan@.
--
-- Precondition: @op@ must be an operator, @op@ must not exist in
-- @pg@, and all the other names in the input have to exist in @pg@.

bindsBetween :: Name -> Assoc -> [Name] -> [Name] ->
                PrecedenceGraph -> PrecedenceGraph
bindsBetween op ass tighterThan looserThan pg@(PG g _)
  | op `containedIn` pg =
      error "bindsBetween: The name is already in the graph."
  | otherwise = case ( fixity op
                     , targetNodes looserThan
                     , targetNodes tighterThan
                     ) of
      (Just f, Just allLooserThan, Just allTighterThan) ->
        PG g' (Map.insert op new (nameMap pg))
        where
        ctxt = ( fix allTighterThan
               , new
               , Map.singleton (ignoreAssoc f ass) (Set.singleton op)
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

prop_bindsBetween pg ass =
  forAll (operatorNotIn pg) $ \op ->
  forAll (namesIn pg) $ \tighterThan ->
  forAll (namesNotBelow tighterThan pg) $ \looserThan ->
    let pg' = bindsBetween op ass tighterThan looserThan pg
        pred `matches` list =
          (pred pg' <$> lookupNode pg' op) ==
          (Set.fromList <$> mapM (lookupNode pg') list)
    in
    graphInvariant pg' &&
    -- The operator is in the graph,
    op `containedIn` pg' &&
    -- directly below looserThan (and nothing else),
    successors `matches` looserThan &&
    -- and directly above tighterThan (and nothing else).
    predecessors `matches` tighterThan &&
    -- Furthermore its associativity is correct.
    associativityCorrect pg' op ass

-- @unrelated op ass pg@ adds a fresh node to @pg@, annotated with
-- @op@ (with associativity @ass@). No new edges are added.

unrelated :: Name -> Assoc -> PrecedenceGraph -> PrecedenceGraph
unrelated op ass = bindsBetween op ass [] []

------------------------------------------------------------------------
-- Generators and other test helpers

instance Arbitrary PrecedenceGraph where
  arbitrary = do
    -- Since names is a set the generated names have to be unique.
    names <- fmap Set.fromList arbitrary
    nodeContents <- partitionsOf =<< pairUp (Set.toList names) arbitrary
    g <- simpleGraph (Maybe.catMaybes $ map mkNode nodeContents)
                     arbitrary
    return (PG g (calculatedNameMap g))
    where
    mkNode :: [(Name, Assoc)] -> Maybe Annotation
    mkNode = ensureNonEmpty .
             Map.fromListWith Set.union .
             map (\(n, ass) ->
                     ( ignoreAssoc (Maybe.fromJust $ fixity n) ass
                     , Set.singleton n )) .
             filter (isOpenOperator . fst)

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

-- | Generates an (open) operator which is not contained in the graph.

operatorNotIn :: PrecedenceGraph -> Gen Name
operatorNotIn pg =
  openOperator `suchThat` \op ->
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
  quickCheck graphInvariant
  quickCheck (all graphInvariant . takeSome . shrink)
  quickCheck prop_nameIn
  quickCheck prop_namesIn
  quickCheck prop_empty
  quickCheck prop_bindsAs
  quickCheck prop_bindsBetween
  where
  takeSome xs = take 10 xs ++ take 10 (drop 200 xs)
