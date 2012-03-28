------------------------------------------------------------------------
-- A variant of the AmbExTrie parsers from Ljunglöf's licentiate thesis
------------------------------------------------------------------------

-- This variant has the advantage of being productive, and is roughly
-- as fast as AmbExTrie.

-- Note that the use of Data.Sequence does not result in any
-- significant performance differences for my mostly unambiguous
-- grammars.

{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses,
             FlexibleInstances #-}

module AmbExTrie2 where

import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Parser
import Control.Applicative
import Data.Sequence (Seq, (><))
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Seq

-- Note that defining noMap = FMap id and removing NoMap makes the
-- code considerably slower, at least in one of my tests (roughly 50%
-- slower).

data Parser k r' tok r
  = forall s. FMap (s -> r) !(Seq s) !(Map tok (Parser k r' tok s))
  | NoMap !(Seq r) !(Map tok (Parser k r' tok r))

instance Functor (Parser k r' tok) where
  fmap f (FMap g xs m) = FMap (f . g) xs m
  fmap f (NoMap xs m)  = FMap f xs m

-- Note that (<|>) is productive. (If we assume a total language.)

instance Ord tok => Alternative (Parser k r' tok) where
  empty = NoMap Seq.empty Map.empty
  NoMap xs1 f1 <|> NoMap xs2 f2 =
    NoMap (xs1 >< xs2) (Map.unionWith (<|>) f1 f2)
  FMap g1 xs1 f1 <|> NoMap xs2 f2 =
    NoMap (fmap g1 xs1 >< xs2)
          (Map.unionWith (<|>) (Map.map (fmap g1) f1) f2)
  NoMap xs1 f1 <|> FMap g2 xs2 f2 =
    NoMap (xs1 >< fmap g2 xs2)
          (Map.unionWith (<|>) f1 (Map.map (fmap g2) f2))
  FMap g1 xs1 f1 <|> FMap g2 xs2 f2 =
    NoMap (fmap g1 xs1 >< fmap g2 xs2)
          (Map.unionWith (<|>) (Map.map (fmap g1) f1)
                               (Map.map (fmap g2) f2))

-- Note that bind is productive.

instance Ord tok => Monad (Parser k r' tok) where
  return x         = NoMap (Seq.singleton x) Map.empty
  NoMap xs f >>= g =
    Seq.foldr (<|>) (NoMap Seq.empty (Map.map (>>= g) f)) (fmap g xs)
  FMap g xs f >>= h =
    Seq.foldr (<|>) (NoMap Seq.empty (Map.map (>>= gh) f)) (fmap gh xs)
    where gh = \x -> h (g x)

instance Ord tok => Applicative (Parser k r' tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> fmap f p2

-- I also simplified parse a little, removing the continuation
-- argument. This didn't significantly affect the timings of my simple
-- test.

-- Note that parse is structurally recursive.

parse :: Ord tok => Parser k r' tok r -> [ tok ] -> [ r ]
parse (NoMap xs f)  []      = Seq.toList xs
parse (NoMap xs f)  (c : s) = case Map.lookup c f of
  Nothing -> []
  Just p' -> parse p' s
parse (FMap g xs f) []      = map g (Seq.toList xs)
parse (FMap g xs f) (c : s) = case Map.lookup c f of
  Nothing -> []
  Just p' -> map g (parse p' s)

instance Ord tok => Parser.Parser (Parser k r' tok) k r' tok where
  sym c = NoMap Seq.empty (Map.singleton c (return c))
