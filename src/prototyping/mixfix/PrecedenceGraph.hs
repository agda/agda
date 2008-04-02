------------------------------------------------------------------------
-- Precedence graphs
------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}

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
  ) where

import Parser
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Graph.Inductive as G
import Data.Graph.Inductive ((&))
import Control.Applicative hiding (empty)
import qualified Control.Applicative as A

------------------------------------------------------------------------
-- Some helper functions

-- [x, y, z] `sepBy'` • ≈ x • y • z.

sepBy' :: Parser p tok => [tok] -> p a -> p [a]
[]       `sepBy'` p = A.empty
[x]      `sepBy'` p = [] <$ sym x
(x : xs) `sepBy'` p = (:) <$> (sym x *> p) <*> (xs `sepBy'` p)

(!) :: Ord k => Map k [v] -> k -> [v]
m ! k = concat $ Map.lookup k m

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
  PG { unPG :: G.Gr (Map Fixity [Name]) () }
     deriving Show

------------------------------------------------------------------------
-- Inspecting precedence graphs

-- | The successors of a node.

successors :: PrecedenceGraph -> Node -> [Node]
successors = G.suc . unPG

-- | A node's annotation.

annotation :: PrecedenceGraph -> Node -> Map Fixity [Name]
annotation g n = case G.lab (unPG g) n of
  Nothing  -> Map.empty
  Just ann -> ann

-- | The nodes in the graph.

nodes :: PrecedenceGraph -> [Node]
nodes = G.nodes . unPG

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
    PG ((pre, n, Map.adjust (op :) fix a, suc) & g')

-- @bindsBetween op fix tighterThan looserThan n g@ adds a new node to
-- @g@, annotated with @op@ (with fixity @fix@). Edges are added from
-- all nodes in @tighterThan@, and their predecessors. Edges are also
-- added to all nodes in @looserThan@, and their successors. The new
-- node label is returned along with the new graph.
--
-- Precondition: The resulting graph has to be acyclic.

bindsBetween :: Name -> Fixity -> [Node] -> [Node] ->
                PrecedenceGraph -> (Node, PrecedenceGraph)
bindsBetween op fix tighterThan looserThan (PG g)
  | acyclic g' = (new, g')
  | otherwise  = error "bindsBetween: Cyclic result."
  where
  [new]          = G.newNodes 1 g
  allLooserThan  = looserThan  ++ concatMap (G.suc g) looserThan
  allTighterThan = tighterThan ++ concatMap (G.pre g) tighterThan
  label          = map ((,) ())
  ctxt           = ( label allTighterThan
                   , new
                   , Map.singleton fix [op]
                   , label allLooserThan
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

-- | Expression parser. Parameterised on a graph describing the
-- operators.

expressionParser :: Parser p Token => PrecedenceGraph -> p Expr
expressionParser g = expr g (nodes g)

-- | Parses atoms.

atom :: Parser p Token => p Expr
atom = AtomE <$ sym Atom

-- | Parses a subset of the expressions. Only the nodes reachable from
-- the given list of nodes are recognised by the parser.

expr :: Parser p Token => PrecedenceGraph -> [Node] -> p Expr
expr g ns = atom <|> choice (map (node g) ns)

-- | Parser for one operator (just the internal, mixfix part).

opProd :: Parser p Token => PrecedenceGraph -> Name -> p Op
opProd g nameParts = (,) (List.intercalate "_" nameParts) <$>
                     (map Name nameParts `sepBy'` expressionParser g)

-- | Parser for several operators.

opProds :: Parser p Token => PrecedenceGraph -> [Name] -> p Op
opProds g ops = choice (map (opProd g) ops)

appLeft :: Expr -> Op -> Expr
appLeft e (n, es) = Op ('_' : n) (e : es)

appRight :: Op -> Expr -> Expr
appRight (n, es) e = Op (n ++ "_") (es ++ [e])

appBoth :: Op -> Expr -> Expr -> Expr
appBoth (n, es) l r = Op ('_' : n ++ "_") (l : es ++ [r])

-- | Parser for a node.

node :: Parser p Token => PrecedenceGraph -> Node -> p Expr
node g n = pre <|> post <|> nonass <|> left <|> right
  where
  ann = annotation g n

  pre    = flip (foldr appRight) <$>
           many1 (opProds g (ann ! Prefix)) <*> higher
  post   = foldl appLeft <$>
           higher <*> many1 (opProds g (ann ! Postfix))
  nonass = flip appBoth <$>
           higher <*> opProds g (ann ! Infix Non) <*> higher
  left   = chainl3 higher (appBoth <$> opProds g (ann ! Infix L))
  right  = chainr3 higher (appBoth <$> opProds g (ann ! Infix R))

  -- Parser for operators of higher precedence.
  higher = expr g (successors g n)
