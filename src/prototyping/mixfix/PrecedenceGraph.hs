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
  , Pos(..)
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
import qualified Control.Applicative as A
import Utilities

------------------------------------------------------------------------
-- Helper functions

-- | Converts a set to a list and maps over it.

map' :: (a -> b) -> Set a -> [b]
map' f = map f . Set.toList

-- | A (safe) variant of 'Map.(!)'.

(!) :: Ord k => Map k (Set v) -> k -> Set v
m ! k = case Map.lookup k m of
  Nothing -> Set.empty
  Just ns -> ns

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

------------------------------------------------------------------------
-- Turning graphs into expression parsers

-- | Tokens. Placeholders are used to indicate sections. Wildcards
-- indicate things the type checker should fill in automatically
-- (hopefully). Names stand for operator name parts (and possibly
-- other identifiers as well).

data Token = Name String | Placeholder Pos | Wildcard | LParen | RParen
  deriving (Eq, Ord, Show)

-- | Placeholder positions.

data Pos = Beg  -- ^ At the beginning of an operator.
         | Mid  -- ^ In the middle of an operator.
         | End  -- ^ At the end of an operator.
  deriving (Eq, Ord, Show)

-- | Expressions.

data Expr = Fun String
          | App Expr [Expr]
            -- ^ Note that the application of an operator to its
            -- arguments is represented using 'Op', not 'App'.
          | Op String [Maybe Expr]
            -- ^ An application of an operator to /all/ its arguments.
            -- 'Nothing' stands for a placeholder.
          | WildcardE
  deriving (Eq, Ord, Show)

-- | Operator applications.

type Op = (String, [Maybe Expr])

-- | Functions for applying 'Op'erator applications to 'Expr'essions.

appLeft :: Maybe Expr -> Op -> Op
appLeft e (n, es) = ('_' : n, e : es)

appRight :: Op -> Maybe Expr -> Op
appRight (n, es) e = (n ++ "_", es ++ [e])

appBoth :: Maybe Expr -> Op -> Maybe Expr -> Op
appBoth e1 o e2 = appLeft e1 (appRight o e2)

-- | Converts an 'Op'erator application to an 'Expr'ession.

toE :: Op -> Expr
toE (n, es) = Op n es

-- | Nonterminals used by the expression grammar.

data NT r where
  ExprN :: Set Node -> NT Expr
  OpN   :: Set Name -> NT Op
  NodeN :: Node     -> NT Expr
  AtomN ::             NT Expr

instance IndexedEq NT where
  iEq (ExprN ns1) (ExprN ns2) = boolToEq $ ns1 == ns2
  iEq (OpN ns1)   (OpN ns2)   = boolToEq $ ns1 == ns2
  iEq (NodeN n1)  (NodeN n2)  = boolToEq $ n1  == n2
  iEq AtomN       AtomN       = Just Refl
  iEq _           _           = Nothing

instance IndexedOrd NT where
  iCompare (ExprN ns1) (ExprN ns2) = compare ns1 ns2
  iCompare (ExprN _)   _           = LT
  iCompare (OpN _)     (ExprN _)   = GT
  iCompare (OpN ns1)   (OpN ns2)   = compare ns1 ns2
  iCompare (OpN _)     _           = LT
  iCompare (NodeN n1)  (ExprN _)   = GT
  iCompare (NodeN n1)  (OpN _)     = GT
  iCompare (NodeN n1)  (NodeN n2)  = compare n1 n2
  iCompare (NodeN n1)  _           = LT
  iCompare AtomN       (ExprN _)   = GT
  iCompare AtomN       (OpN _)     = GT
  iCompare AtomN       (NodeN _)   = GT
  iCompare AtomN       AtomN       = EQ

-- | Non-terminal for an expression.

expression :: PrecedenceGraph -> NT Expr
expression g = ExprN (nodes g)

-- | A placeholder of the given kind.

placeholder :: NTParser p NT Token => Pos -> p (Maybe Expr)
placeholder p = Nothing <$ sym (Placeholder p)

-- | The expression grammar.

grammar :: NTParser p NT Token =>
           PrecedenceGraph ->
           -- ^ The precedence graph.
           p String ->
           -- ^ Parser for identifiers/function names (not operator
           -- name parts).
           Set Name ->
           -- ^ Closed mixfix operators.
           NT r -> p r

-- Note that parentheses should not be treated here. The top-level
-- parser should take care of let, lambda, parentheses, hidden
-- argument braces, and pattern dots. (And perhaps something else as
-- well.)

-- Note also that an operator which is sectioned in the right way
-- becomes closed.

grammar g identifier closed AtomN =
      Fun <$> identifier
  <|> WildcardE <$ sym Wildcard
  <|> sym LParen *> nonTerm (expression g) <* sym RParen
  <|> toE <$> (      nonTerm (OpN closed)
    <|> appRight <$> nonTerm (OpN prefix) <*> placeholder End
    <|> appLeft  <$> placeholder Beg <*> nonTerm (OpN postfix)
    <|> appBoth  <$> placeholder Beg <*> nonTerm (OpN infx) <*>
                     placeholder End)
  where
  allOps  = allOperators g
  prefix  = allOps ! Prefix
  postfix = allOps ! Postfix
  infx    = allInfix allOps

-- Production for a subset of the expressions. Only the nodes
-- reachable from the given set of nodes are recognised.

grammar _ _ _ (ExprN ns)
   =  nonTerm AtomN
  <|> App <$> nonTerm AtomN <*> many1 (nonTerm AtomN)
  <|> choice (map' (nonTerm . NodeN) ns)

-- Production for operators (just the internal, mixfix parts; not the
-- "outer" arguments).

grammar g _ _ (OpN ops) = choice $ map' op ops
  where
  op nameParts =
    (,) (List.intercalate "_" nameParts) <$>
        (Just <$> nonTerm (expression g) <|> placeholder Mid)
          `between`
        map Name nameParts

-- Production for a graph node.

grammar g _ _ (NodeN n) = choice $
  [ flip (foldr appRight') <$> many1 (internal Prefix) <*> higher
  , foldl appLeft'         <$> higher <*> many1 (internal Postfix)
  , appBoth' <$> higher <*> internal (Infix Non) <*> higher
  , chainl3 higher (flip appBoth' <$> internal (Infix L))
  , chainr3 higher (flip appBoth' <$> internal (Infix R))
  ]
  where
  -- Operators of higher precedence or atoms.
  higher = nonTerm (ExprN (successors g n))

  -- The internal parts of operators of the given fixity (in this
  -- node). Includes certain sections; for instance, a left-sectioned
  -- infix operator becomes a prefix operator.
  internal f =  nonTerm (OpN (ann ! f))
            <|> case f of
                  Prefix  -> appLeft  <$> placeholder Beg <*> infx
                  Postfix -> appRight <$> infx <*> placeholder End
                  Infix _ -> A.empty
    where
    ann  = annotation g n
    infx = nonTerm (OpN (allInfix ann))

  appLeft'  e o     = toE $ appLeft  (Just e) o
  appRight' o e     = toE $ appRight o (Just e)
  appBoth'  e1 o e2 = toE $ appBoth  (Just e1) o (Just e2)
