------------------------------------------------------------------------
-- A variant of the AmbExTrie parsers from Ljunglöf's licentiate thesis
------------------------------------------------------------------------

-- This variant has the advantage of being productive, and is roughly
-- as fast as AmbExTrie.

{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses,
             FlexibleInstances #-}

module AmbExTrie2 where

import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Parser
import Control.Applicative

-- Note that defining noMap = FMap id and removing NoMap makes the
-- code considerably slower, at least in my test (roughly 50% slower).

data Parser tok r
  = forall s. FMap (s -> r) ![ s ] !(Map tok (Parser tok s))
  | NoMap ![ r ] !(Map tok (Parser tok r))

instance Functor (Parser tok) where
  fmap f (FMap g xs m) = FMap (f . g) xs m
  fmap f (NoMap xs m)  = FMap f xs m

-- Note that (<|>) is productive. (If we assume a total language.)

instance Ord tok => Alternative (Parser tok) where
  empty = NoMap [] Map.empty
  NoMap xs1 f1 <|> NoMap xs2 f2 =
    NoMap (xs1 ++ xs2) (Map.unionWith (<|>) f1 f2)
  FMap g1 xs1 f1 <|> NoMap xs2 f2 =
    NoMap (map g1 xs1 ++ xs2)
          (Map.unionWith (<|>) (Map.map (fmap g1) f1) f2)
  NoMap xs1 f1 <|> FMap g2 xs2 f2 =
    NoMap (xs1 ++ map g2 xs2)
          (Map.unionWith (<|>) f1 (Map.map (fmap g2) f2))
  FMap g1 xs1 f1 <|> FMap g2 xs2 f2 =
    NoMap (map g1 xs1 ++ map g2 xs2)
          (Map.unionWith (<|>) (Map.map (fmap g1) f1)
                               (Map.map (fmap g2) f2))

-- Note that bind is productive.

instance Ord tok => Monad (Parser tok) where
  return x         = NoMap [x] Map.empty
  NoMap xs f >>= g =
    foldr (<|>) (NoMap [] (Map.map (>>= g) f)) (map g xs)
  FMap g xs f >>= h =
    foldr (<|>) (NoMap [] (Map.map (>>= gh) f)) (map gh xs)
    where gh = \x -> h (g x)

instance Ord tok => Applicative (Parser tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> fmap f p2

-- I also simplified parse a little, removing the continuation
-- argument. This didn't significantly affect the timings of my simple
-- test.

-- Note that parse is structurally recursive.

parse :: Ord tok => Parser tok r -> [ tok ] -> [ r ]
parse (NoMap xs f)  []      = xs
parse (NoMap xs f)  (c : s) = case Map.lookup c f of
  Nothing -> []
  Just p' -> parse p' s
parse (FMap g xs f) []      = map g xs
parse (FMap g xs f) (c : s) = case Map.lookup c f of
  Nothing -> []
  Just p' -> map g (parse p' s)

instance Ord tok => Parser.Parser (Parser tok) tok where
  sym c = NoMap [] (Map.singleton c (return c))
  parse = parse