------------------------------------------------------------------------
-- The AmbTrie parsers from Ljunglöf's licentiate thesis
------------------------------------------------------------------------

-- I added some strictness annotations.

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module AmbTrie where

import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Parser
import Control.Applicative

infix 4 :&:

data Parser k r' tok r = ![ r ] :&: !(Map tok (Parser k r' tok r))

instance Ord tok => Functor (Parser k r' tok) where
  fmap = liftM

-- Note that (<|>) is productive. (If we assume a total language.)

instance Ord tok => Alternative (Parser k r' tok) where
  empty                     = [] :&: Map.empty
  xs1 :&: f1 <|> xs2 :&: f2 =
    xs1 ++ xs2 :&: Map.unionWith (<|>) f1 f2

-- Note that bind is productive.

instance Ord tok => Monad (Parser k r' tok) where
  return x       = [x] :&: Map.empty
  xs :&: f >>= g = foldr (<|>) ([] :&: Map.map (>>= g) f) (map g xs)

instance Ord tok => Applicative (Parser k r' tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> p2 >>= \x -> return (f x)

-- Note that parse is structurally recursive.

parse :: Ord tok => Parser k r' tok r -> [ tok ] -> [ r ]
parse (xs :&: f) []      = xs
parse (xs :&: f) (c : s) = case Map.lookup c f of
  Nothing -> []
  Just f' -> parse f' s

instance Ord tok => Parser.Parser (Parser k r' tok) k r' tok where
  sym c = [] :&: Map.singleton c (return c)
