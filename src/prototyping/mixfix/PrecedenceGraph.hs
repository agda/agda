------------------------------------------------------------------------
-- Precedence graphs
------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts, GADTs #-}

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
  , NT
  , expression
  , grammar
  ) where

import Parser
import IndexedOrd
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive ((&))
import Control.Applicative hiding (empty)
import Utilities

------------------------------------------------------------------------
-- Some helper functions

-- | Converts a set to a list and maps over it.

map' :: (a -> b) -> Set a -> [b]
map' f = map f . Set.toList

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

-- | Functions for building Expressions.

appLeft :: Expr -> Op -> Expr
appLeft e (n, es) = Op ('_' : n) (e : es)

appRight :: Op -> Expr -> Expr
appRight (n, es) e = Op (n ++ "_") (es ++ [e])

appBoth :: Op -> Expr -> Expr -> Expr
appBoth (n, es) l r = Op ('_' : n ++ "_") (l : es ++ [r])

-- | Nonterminals used by the expression grammar.

data NT r where
  ExprN :: Set Node -> NT Expr
  OpN   :: Set Name -> NT Op
  NodeN :: Node     -> NT Expr

instance IndexedEq NT where
  iEq (ExprN ns1) (ExprN ns2) = boolToEq $ ns1 == ns2
  iEq (OpN ns1)   (OpN ns2)   = boolToEq $ ns1 == ns2
  iEq (NodeN n1)  (NodeN n2)  = boolToEq $ n1  == n2
  iEq _           _           = Nothing

instance IndexedOrd NT where
  iCompare (ExprN ns1) (ExprN ns2) = compare ns1 ns2
  iCompare (ExprN _)   _           = LT
  iCompare (OpN _)     (ExprN _)   = GT
  iCompare (OpN ns1)   (OpN ns2)   = compare ns1 ns2
  iCompare (OpN _)     _           = LT
  iCompare (NodeN n1)  (NodeN n2)  = compare n1 n2
  iCompare (NodeN n1)  _           = GT

-- | Non-terminal for an expression.

expression :: PrecedenceGraph -> NT Expr
expression g = ExprN (nodes g)

-- | The expression grammar.

grammar :: NTParser p NT Token => PrecedenceGraph -> NT r -> p r

-- Production for a subset of the expressions. Only the nodes
-- reachable from the given set of nodes are recognised.
--
-- Note that Atom stands for applications of one or more identifiers,
-- parenthesised expressions, or mixfix operators that are not prefix,
-- postfix or infix. Hence the atom parser will probably be
-- implemented as part of, or using, this grammar.

grammar g (ExprN ns) =  AtomE <$ sym Atom
                    <|> choice (map' (nonTerm . NodeN) ns)

-- Production for operators (just the internal, mixfix parts; not the
-- "outer" arguments).

grammar g (OpN ops) = choice $ map' op ops
  where
  op nameParts =
    (,) (List.intercalate "_" nameParts) <$>
        nonTerm (expression g) `between` map Name nameParts

-- Production for a graph node.

grammar g (NodeN n) = choice $
  [ flip (foldr appRight) <$> many1 (int Prefix) <*> h
  , foldl appLeft         <$> h <*> many1 (int Postfix)
  , flip appBoth <$> h <*> int (Infix Non) <*> h
  , chainl3 h (appBoth <$> int (Infix L))
  , chainr3 h (appBoth <$> int (Infix R))
  ]
  where
  -- Operators of higher precedence.
  h = nonTerm $ ExprN (successors g n)

  -- The internal parts of operators of the given fixity (in this
  -- node).
  int fixity = nonTerm $ OpN (annotation g n ! fixity)

  m ! k = case Map.lookup k m of
    Nothing -> Set.empty
    Just ns -> ns
