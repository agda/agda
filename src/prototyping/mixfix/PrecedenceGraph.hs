------------------------------------------------------------------------
-- Precedence graphs
------------------------------------------------------------------------

{-# OPTIONS_GHC -fglasgow-exts #-} -- LiberalTypeSynonyms does not work.
{-# LANGUAGE FlexibleContexts, LiberalTypeSynonyms #-}

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
import qualified Control.Monad.State as S
import qualified Control.Monad.Identity as I

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
bindsBetween op fixity tighterThan looserThan (PG g)
  | acyclic g' = (new, g')
  | otherwise  = error "bindsBetween: Cyclic result."
  where
  [new]          = G.newNodes 1 g
  allLooserThan  = looserThan  ++ concatMap (G.suc g) looserThan
  allTighterThan = tighterThan ++ concatMap (G.pre g) tighterThan
  fix            = map ((,) ()) . List.nub
  ctxt           = ( fix allTighterThan
                   , new
                   , Map.singleton fixity [op]
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

type P r = forall p. Parser p Token =>
           S.State (Map Node (p Expr)) (p r)

-- | Expression parser. Parameterised on a graph describing the
-- operators.

expressionParser :: Parser p Token => PrecedenceGraph -> p Expr
expressionParser g = S.evalState (expr g (nodes g)) Map.empty

-- | Parses a subset of the expressions. Only the nodes reachable from
-- the given list of nodes are recognised by the parser.

expr :: PrecedenceGraph -> [Node] -> P Expr
expr g ns = do
  ns <- mapM (node g) ns
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
           (map Name nameParts `sepBy'` expressionParser g)

-- | Parser for several operators.

opProds :: PrecedenceGraph -> [Name] -> P Op
opProds g ops = fmap choice (mapM (opProd g) ops)

appLeft :: Expr -> Op -> Expr
appLeft e (n, es) = Op ('_' : n) (e : es)

appRight :: Op -> Expr -> Expr
appRight (n, es) e = Op (n ++ "_") (es ++ [e])

appBoth :: Op -> Expr -> Expr -> Expr
appBoth (n, es) l r = Op ('_' : n ++ "_") (l : es ++ [r])

-- | Parser for a node.

-- The graph typically has lots of sharing (many pointers to the same
-- node), so this function is memoised.

node :: PrecedenceGraph -> Node -> P Expr
node g n = do
  memoisedP <- fmap (Map.lookup n) S.get
  case memoisedP of
    Just p  -> return p
    Nothing -> do
      -- Parser for operators of higher precedence.
      h <- expr g (successors g n)
      p <- fmap choice $ sequence (opParsers h)
      S.modify (Map.insert n p)
      return p
  where
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
