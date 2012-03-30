------------------------------------------------------------------------
-- Turning graphs into expression parsers
------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts, GADTs #-}

module ExpressionParser
  ( NT
  , parse
  ) where

import qualified Parser
import Parser hiding (parse)
import PrecedenceGraph
import Utilities
import IndexedOrd
import Name
import Token
import Expression
import qualified MemoisedCPS

import Control.Applicative as A
import Data.Foldable (asum)
import qualified Data.List as List
import qualified Data.Set  as Set
import Data.Set (Set)

-- | Looks up all names of the given fixity, regardless of the
-- annotation.

(!*) :: Annotation -> Fixity -> Set Name
m !* k = Set.unions [m ! (k, ass) | ass <- [Non, L, R]]

-- | Operator applications.

type Op = (Name, [Maybe Expr])

-- | Functions for applying 'Op'erator applications to 'Expr'essions.

appLeft :: Maybe Expr -> Op -> Op
appLeft e (u, es) = (u, e : es)

appRight :: Op -> Maybe Expr -> Op
appRight (u, es) e = (u, es ++ [e])

appBoth :: Maybe Expr -> Op -> Maybe Expr -> Op
appBoth e1 o e2 = appLeft e1 (appRight o e2)

-- | Converts an 'Op'erator application to an 'Expr'ession.

toE :: Op -> Expr
toE (u, es) = Op u es

-- | Nonterminals used by the expression grammar.

data NT r where
  ExprN      :: Set Node -> NT Expr
  OpN        :: Set Name -> NT Op
  NodeN      :: Node     -> NT Expr
  PostLeftsN :: Node     -> NT Expr
  AtomN      ::             NT Expr

-- | Non-terminal for an expression.

expression :: PrecedenceGraph -> NT Expr
expression g = ExprN (nodes g)

-- | A placeholder of the given kind.

placeholder :: NTParser p NT Token => Pos -> p (Maybe Expr)
placeholder p = Nothing <$ sym (Placeholder p)

-- | Parses the given name part (possibly with a shorter module
-- prefix).

namePart :: NTParser p NT Token
         => [String]
         -- ^ Module name.
         -> String
         -- ^ Name part.
         -> p ()
namePart ms n = symbol >>= \s -> case s of
  QualifiedName ms' n' -> if ms' `List.isSuffixOf` ms && n' == n
                          then return () else A.empty
  _ -> A.empty

-- | The expression grammar.

grammar :: NTParser p NT Token =>
           PrecedenceGraph ->
           -- ^ The precedence graph.
           (Name -> Set Name) ->
           -- ^ A function giving all qualified names matching the
           -- given qualified name (which might be given with an
           -- incomplete module name prefix).
           Set Name ->
           -- ^ Closed mixfix operators.
           NT r -> p r

-- Note that parentheses should not be treated here. The top-level
-- parser should take care of let, lambda, parentheses, hidden
-- argument braces, and pattern dots. (And perhaps something else as
-- well.)

-- Note also that an operator which is sectioned in the right way
-- becomes closed.

grammar g lookupName closed AtomN =
      Fun <$> (asum =<< map return . filter (not . isOperator) .
                        Set.toList . lookupName <$> parseName)
  <|> WildcardE <$ sym Wildcard
  <|> sym LParen *> nonTerm (expression g) <* sym RParen
  <|> toE <$> (      nonTerm (OpN closed)
    <|> appRight <$> nonTerm (OpN prefix) <*> placeholder End
    <|> appLeft  <$> placeholder Beg <*> nonTerm (OpN postfix)
    <|> appBoth  <$> placeholder Beg <*> nonTerm (OpN infx) <*>
                     placeholder End)
  where
  allOps  = allOperators g
  prefix  = allOps !* Prefix
  postfix = allOps !* Postfix
  infx    = allOps !* Infix

-- Production for a subset of the expressions. Only the nodes
-- reachable from the given set of nodes are recognised.

grammar _ _ _ (ExprN ns)
   =  app <$> nonTerm AtomN <*> many (nonTerm AtomN)
  <|> asum (map (nonTerm . NodeN) $ Set.toList ns)

-- Production for operators (just the internal, mixfix parts; not the
-- "outer" arguments).

grammar g _ _ (OpN ops) = asum $ map op (Set.toList ops)
  where
  op n = (,) n <$>
    (Just <$> nonTerm (expression g) <|> placeholder Mid)
      `between`
    map (namePart (moduleName n)) (nameParts n)

-- Production for a graph node.

grammar g _ _ (NodeN n) =
  nonAssoc <|> preRights <|> nonTerm (PostLeftsN n)
  where
  -- Applications of non-associative operators.
  nonAssoc = appBoth' <$>
    higher g n <*> internal g n Infix Non <*> higher g n

  -- Sequences of prefix/infix right-associative operators.
  preRights = preRight <*> (preRights <|> higher g n)
    where
    preRight =  appRight' <$>                internal g n Prefix Non
            <|> appBoth'  <$> higher g n <*> internal g n Infix  R

  appRight'    o e2 = toE $ appRight           o (Just e2)
  appBoth'  e1 o e2 = toE $ appBoth  (Just e1) o (Just e2)

-- Sequences of postfix/infix left-associative operators. (This
-- non-terminal needs to be memoised: it is left recursive.)

grammar g _ _ (PostLeftsN n) = flip ($) <$>
  (nonTerm (PostLeftsN n) <|> higher g n) <*> postLeft
  where
  postLeft =  appLeft' <$> internal g n Postfix Non
          <|> appBoth' <$> internal g n Infix   L   <*> higher g n

  appLeft' o    e1 = toE $ appLeft (Just e1) o
  appBoth' o e2 e1 = toE $ appBoth (Just e1) o (Just e2)

-- | Production for the internal parts of operators of the given
-- fixity (in this node). Includes certain sections; for instance, a
-- left-sectioned infix operator becomes a prefix operator.

internal :: NTParser p NT Token =>
            PrecedenceGraph -> Node -> Fixity -> Assoc -> p Op
internal g n f ass =
      nonTerm (OpN (ann ! (f, ass)))
  <|> case f of
        Prefix  -> appLeft  <$> placeholder Beg <*> infx
        Postfix -> appRight <$> infx <*> placeholder End
        Infix   -> A.empty
  where
  ann  = annotation g n
  infx = nonTerm (OpN (ann !* Infix))

-- | Production for expressions of higher precedence or atoms.

higher :: NTParser p NT Token =>
          PrecedenceGraph -> Node -> p Expr
higher g n = nonTerm (ExprN (successors g n))

-- | Parses an expression.

parse :: PrecedenceGraph ->
         -- ^ The precedence graph.
         (Name -> Set Name) ->
         -- ^ A function giving all qualified names matching the
         -- given qualified name (which might be given with an
         -- incomplete module name prefix).
         Set Name ->
         -- ^ Closed mixfix operators.
         [Token] ->
         -- ^ Input tokens.
         [Expr]
parse g lookupName closed =
  MemoisedCPS.parse (grammar g lookupName closed)
                    (nonTerm $ expression g)

------------------------------------------------------------------------
-- Boring instances

instance IndexedEq NT where
  iEq (ExprN ns1)     (ExprN ns2)     = boolToEq $ ns1 == ns2
  iEq (OpN ns1)       (OpN ns2)       = boolToEq $ ns1 == ns2
  iEq (NodeN n1)      (NodeN n2)      = boolToEq $ n1  == n2
  iEq (PostLeftsN n1) (PostLeftsN n2) = boolToEq $ n1  == n2
  iEq AtomN           AtomN           = Just Refl
  iEq _               _               = Nothing

instance IndexedOrd NT where
  iCompare (ExprN ns1)     (ExprN ns2)     = compare ns1 ns2
  iCompare (OpN ns1)       (OpN ns2)       = compare ns1 ns2
  iCompare (NodeN n1)      (NodeN n2)      = compare n1 n2
  iCompare (PostLeftsN n1) (PostLeftsN n2) = compare n1 n2
  iCompare AtomN           AtomN           = EQ
  iCompare (ExprN _)       _               = LT
  iCompare (OpN _)         (ExprN _)       = GT
  iCompare (OpN _)         _               = LT
  iCompare (NodeN _)       (ExprN _)       = GT
  iCompare (NodeN _)       (OpN _)         = GT
  iCompare (NodeN _)       _               = LT
  iCompare (PostLeftsN _)  AtomN           = LT
  iCompare (PostLeftsN _)  _               = GT
  iCompare AtomN           _               = GT
