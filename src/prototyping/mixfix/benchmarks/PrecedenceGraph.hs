------------------------------------------------------------------------
-- Precedence graphs
------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts, Rank2Types #-}

module PrecedenceGraph
    -- * Precedence graphs.
  ( Name
  , Assoc(..)
  , Fixity(..)
  , Node
  , PrecedenceGraph
    -- * Constructing precedence graphs.
  , empty
  , bindsAs
  , bindsBetween
  , unrelated
    -- * Parsing expressions.
  , Token(..)
  , Expr(..)
  , expressionParser
    -- * Testing.
  , tests
  ) where

import Parser
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive ((&))
import Control.Applicative hiding (empty)
import Control.Monad
import qualified Control.Applicative as A
import qualified Control.Monad.State as S
import qualified Control.Monad.Identity as I
import Data.Function
import Test.QuickCheck

------------------------------------------------------------------------
-- Some helper functions

-- | Converts a set to a list and maps over it.

mapM' :: Monad m => (a -> m b) -> Set a -> m [b]
mapM' f = mapM f . Set.toList

-- | An efficient variant of 'List.nub'.

efficientNub :: Ord a => [a] -> [a]
efficientNub = removeDups . List.sort
  where removeDups = map head . List.group

-- Code used to test efficientNub.

data IgnoreSnd a b = Pair a b
  deriving Show

fst' :: IgnoreSnd a b -> a
fst' (Pair x y) = x

instance (Eq a, Eq b) => Eq (IgnoreSnd a b) where
  (==) = (==) `on` fst'

instance (Ord a, Eq b) => Ord (IgnoreSnd a b) where
  compare = compare `on` fst'

instance (Arbitrary a, Arbitrary b) => Arbitrary (IgnoreSnd a b) where
  arbitrary = liftM2 Pair arbitrary arbitrary

-- | This property tests that 'efficientNub' is equivalent to 'nub',
-- up to a permutation of the output. Note that the property checks
-- that the two functions choose the same representative from every
-- equivalence class.

prop_efficientNub :: [IgnoreSnd Integer Int] -> Property
prop_efficientNub xs =
  classify nonTriv "with non-trivial equivalence classes" $
    efficientNub xs =*= List.sort (List.nub xs)
  where
  xs =*= ys = length xs == length ys && and (zipWith reallyEqual xs ys)
  reallyEqual (Pair x y) (Pair u v) = x == u && y == v

  nonTriv = any ((> 1) . length) $
            map (List.nubBy reallyEqual) $
            List.group $ List.sort xs

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
  -- The test for acyclicity is rather slow.
  | True {- acyclic g' -} = (new, g')
  | otherwise             = error "bindsBetween: Cyclic result."
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

------------------------------------------------------------------------
-- Turning graphs into expression parsers

-- | Tokens.

data Token = Atom | Name String
  deriving (Eq, Ord, Show)

-- | Expressions.

data Expr = AtomE | Op String [Expr]
  deriving (Eq, Ord, Show)

-- | The internal, mixfix part of an operator (the name, excluding outer
-- '_', plus the internal expressions).

type Op = (String, [Expr])

-- | The parser type used below. The state component is used to
-- memoise the computation of node parsers.

type P r = forall p. Parser p Node Expr Token =>
           S.State (Map Node (p Expr)) (p r)

-- | Expression parser. Parameterised on a graph describing the
-- operators.

expressionParser :: Parser p Node Expr Token =>
                    PrecedenceGraph -> p Expr
expressionParser g = S.evalState (expr g (nodes g)) Map.empty

-- | Parses a subset of the expressions. Only the nodes reachable from
-- the given list of nodes are recognised by the parser.

-- Note that Atom stands for applications of one or more identifiers,
-- parenthesised expressions, or mixfix operators that are not prefix,
-- postfix or infix. Hence the atom parser will probably be
-- implemented using expressionParser.

expr :: PrecedenceGraph -> Set Node -> P Expr
expr g ns = do
  ns <- mapM' (node g) ns
  return $ (AtomE <$ sym Atom) <|> choice ns

-- | Parser for one operator (just the internal, mixfix part).

-- Note that this function uses the non-memoised (expressionParser g)
-- instead of the memoised (expr g (nodes g)). The reason is that
-- otherwise the memoisation is not sufficiently productive. This
-- could be fixed by inserting the parsers into the memo table
-- _before_ computing them, by using recursive do in "node" below.
-- However, I think recursive do is too complicated. The current
-- solution is easier to understand and gives roughly the same
-- performance.

opProd :: PrecedenceGraph -> Name -> P Op
opProd g nameParts =
  return $ (,) (List.intercalate "_" nameParts) <$>
           (expressionParser g `between` map Name nameParts)

-- | Parser for several operators.

opProds :: PrecedenceGraph -> Set Name -> P Op
opProds g ops = fmap choice (mapM' (opProd g) ops)

appLeft :: Expr -> Op -> Expr
appLeft e (n, es) = Op ('_' : n) (e : es)

appRight :: Op -> Expr -> Expr
appRight (n, es) e = Op (n ++ "_") (es ++ [e])

appBoth :: Op -> Expr -> Expr -> Expr
appBoth (n, es) l r = Op ('_' : n ++ "_") (l : es ++ [r])

-- | Parser for a node.
--
-- The graph typically has lots of sharing (many pointers to the same
-- node), so this function is memoised. In two ways, actually:
--
-- 1) The construction of the parsers is memoised.
--
-- 2) If a memoising parser is used the results of parsing a given
--    node at a specific position are also memoised.
--
-- Note that the second memoisation is potentially unsafe, if this
-- parser is combined with another memoised parser. The memoisation
-- keys have to be unique.

node :: PrecedenceGraph -> Node -> P Expr
node g n = do
  memoisedP <- fmap (Map.lookup n) S.get
  case memoisedP of
    Just p  -> return p
    Nothing -> do
      -- Parser for operators of higher precedence.
      h <- expr g (successors g n)
      p <- fmap (memoise n . choice) $ sequence (opParsers h)
      S.modify (Map.insert n p)
      return p
  where
  m ! k = case Map.lookup k m of
    Nothing -> Set.empty
    Just ns -> ns

  ops fixity f = fmap f (opProds g (annotation g n ! fixity))
                        -- Parser for the internal parts of operators
                        -- of the given fixity (in this node).

  opParsers h =
    [ ops Prefix      (\o -> flip (foldr appRight) <$> many1 o <*> h)
    , ops Postfix     (\o -> foldl appLeft         <$> h <*> many1 o)
    , ops (Infix Non) (\o -> flip appBoth <$> h <*> o <*> h)
    , ops (Infix L)   (\o -> chainl3 h (appBoth <$> o))
    , ops (Infix R)   (\o -> chainr3 h (appBoth <$> o))
    ]

------------------------------------------------------------------------
-- All test cases

-- | All tests from this module.

tests = do
  quickCheck prop_efficientNub
