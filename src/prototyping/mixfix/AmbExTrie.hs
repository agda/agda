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

{-# LANGUAGE ExistentialQuantification #-}

module AmbExTrie where

import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Parser

infix 4 :&:

data Parser tok r
  = ![ r ] :&: !(Map tok (Parser tok r))
  | forall s. FMap (s -> r) (Parser tok s)

instance Functor (Parser tok) where
  fmap = FMap

unfold :: Ord tok => (s -> r) -> Parser tok s -> Parser tok r
unfold f (xs :&: g) = map f xs :&: Map.map (FMap f) g
unfold f (FMap g p) = FMap (f . g) p

instance Ord tok => MonadPlus (Parser tok) where
  mzero                           = [] :&: Map.empty
  mplus (xs1 :&: f1) (xs2 :&: f2) =
    xs1 ++ xs2 :&: Map.unionWith mplus f1 f2
  mplus (FMap f p1)  p2           = mplus (unfold f p1) p2
  mplus p1           (FMap f p2)  = mplus p1 (unfold f p2)

instance Ord tok => Monad (Parser tok) where
  return x       = [x] :&: Map.empty
  xs :&: f >>= g = foldr mplus ([] :&: Map.map (>>= g) f) (map g xs)
  FMap f p >>= g = unfold f p >>= g

(<*>) :: Ord tok => Parser tok (s -> r) -> Parser tok s -> Parser tok r
p1 <*> p2 = p1 >>= \f -> fmap f p2

sym :: Ord tok => tok -> Parser tok tok
sym c = [] :&: Map.singleton c (return c)

parse :: Ord tok => Parser tok r -> [ tok ] -> [ r ]
parse p s = parse' p s id
  where
  parse' :: Ord tok => Parser tok s -> [ tok ] -> (s -> r) -> [ r ]
  parse' (xs :&: f) []      k = map k xs
  parse' (xs :&: f) (c : s) k = case Map.lookup c f of
    Nothing -> []
    Just p' -> parse' p' s k
  parse' (FMap f p) xs      k = parse' p xs (k . f)

instance Parser.Parser Parser where
  ret   = return
  (<*>) = (<*>)
  zero  = mzero
  (<|>) = mplus
  sym   = sym
  parse = parse
