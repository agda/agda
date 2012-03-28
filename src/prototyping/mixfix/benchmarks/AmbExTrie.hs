------------------------------------------------------------------------
-- The AmbExTrie parsers from Ljunglöf's licentiate thesis
------------------------------------------------------------------------

-- I added some strictness annotations (but only for "inductive"
-- arguments).

-- Note that mplus below is not productive:
--
--   let p = FMap id p in mplus p p
--
-- does not produce any output.

{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses,
             FlexibleInstances #-}

module AmbExTrie where

import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Parser
import Control.Applicative

infix 4 :&:

data Parser k r' tok r
  = ![ r ] :&: !(Map tok (Parser k r' tok r))
  | forall s. FMap (s -> r) (Parser k r' tok s)

instance Functor (Parser k r' tok) where
  fmap = FMap

unfold :: Ord tok => (s -> r) -> Parser k r' tok s -> Parser k r' tok r
unfold f (xs :&: g) = map f xs :&: Map.map (FMap f) g
unfold f (FMap g p) = FMap (f . g) p

instance Ord tok => Alternative (Parser k r' tok) where
  empty                     = [] :&: Map.empty
  xs1 :&: f1 <|> xs2 :&: f2 = xs1 ++ xs2 :&: Map.unionWith (<|>) f1 f2
  FMap f p1  <|> p2         = unfold f p1 <|> p2
  p1         <|> FMap f p2  = p1 <|> unfold f p2

instance Ord tok => Monad (Parser k r' tok) where
  return x       = [x] :&: Map.empty
  xs :&: f >>= g = foldr (<|>) ([] :&: Map.map (>>= g) f) (map g xs)
  FMap f p >>= g = unfold f p >>= g

instance Ord tok => Applicative (Parser k r' tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> fmap f p2

parse :: Ord tok => Parser k r' tok r -> [ tok ] -> [ r ]
parse p s = parse' p s id
  where
  parse' :: Ord tok => Parser k r' tok s -> [ tok ] -> (s -> r) -> [ r ]
  parse' (xs :&: f) []      k = map k xs
  parse' (xs :&: f) (c : s) k = case Map.lookup c f of
    Nothing -> []
    Just p' -> parse' p' s k
  parse' (FMap f p) xs      k = parse' p xs (k . f)

instance Ord tok => Parser.Parser (Parser k r' tok) k r' tok where
  sym c = [] :&: Map.singleton c (return c)
