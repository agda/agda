------------------------------------------------------------------------
-- A variant of the AmbExTrie parsers from Ljunglöf's licentiate thesis
------------------------------------------------------------------------

-- This variant has the advantage of being productive, and is roughly
-- as fast as AmbExTrie.

{-# LANGUAGE ExistentialQuantification #-}

module AmbExTrie2 where

import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Parser

-- Note that defining noMap = FMap id and removing NoMap makes the
-- code considerably slower, at least in my test (roughly 50% slower).

data Parser tok r
  = forall s. FMap (s -> r) ![ s ] !(Map tok (Parser tok s))
  | NoMap ![ r ] !(Map tok (Parser tok r))

instance Functor (Parser tok) where
  fmap f (FMap g xs m) = FMap (f . g) xs m
  fmap f (NoMap xs m)  = FMap f xs m

-- Note that mplus is productive. (If we assume a total language.)

instance Ord tok => MonadPlus (Parser tok) where
  mzero = NoMap [] Map.empty
  mplus (NoMap xs1 f1) (NoMap xs2 f2) =
    NoMap (xs1 ++ xs2) (Map.unionWith mplus f1 f2)
  mplus (FMap g1 xs1 f1) (NoMap xs2 f2) =
    NoMap (map g1 xs1 ++ xs2)
          (Map.unionWith mplus (Map.map (fmap g1) f1) f2)
  mplus (NoMap xs1 f1) (FMap g2 xs2 f2) =
    NoMap (xs1 ++ map g2 xs2)
          (Map.unionWith mplus f1 (Map.map (fmap g2) f2))
  mplus (FMap g1 xs1 f1) (FMap g2 xs2 f2) =
    NoMap (map g1 xs1 ++ map g2 xs2)
          (Map.unionWith mplus (Map.map (fmap g1) f1)
                               (Map.map (fmap g2) f2))

-- Note that bind is productive.

instance Ord tok => Monad (Parser tok) where
  return x         = NoMap [x] Map.empty
  NoMap xs f >>= g =
    foldr mplus (NoMap [] (Map.map (>>= g) f)) (map g xs)
  FMap g xs f >>= h =
    foldr mplus (NoMap [] (Map.map (>>= gh) f)) (map gh xs)
    where gh = \x -> h (g x)

(<*>) :: Ord tok => Parser tok (s -> r) -> Parser tok s -> Parser tok r
p1 <*> p2 = p1 >>= \f -> fmap f p2

sym :: Ord tok => tok -> Parser tok tok
sym c = NoMap [] (Map.singleton c (return c))

-- I also simplified this function a little, removing the continuation
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

instance Parser.Parser Parser where
  ret   = return
  (<*>) = (<*>)
  zero  = mzero
  (<|>) = mplus
  sym   = sym
  parse = parse
