------------------------------------------------------------------------
-- The AmbTrie parsers from Ljunglöf's licentiate thesis
------------------------------------------------------------------------

-- I added some strictness annotations.

module AmbTrie where

import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Parser

infix 4 :&:

data Parser tok r = ![ r ] :&: !(Map tok (Parser tok r))

-- Note that mplus is productive. (If we assume a total language.)

instance Ord tok => MonadPlus (Parser tok) where
  mzero                           = [] :&: Map.empty
  mplus (xs1 :&: f1) (xs2 :&: f2) =
    xs1 ++ xs2 :&: Map.unionWith mplus f1 f2

-- Note that bind is productive.

instance Ord tok => Monad (Parser tok) where
  return x       = [x] :&: Map.empty
  xs :&: f >>= g = foldr mplus ([] :&: Map.map (>>= g) f) (map g xs)

sym :: Ord tok => tok -> Parser tok tok
sym c = [] :&: Map.singleton c (return c)

-- Note that parse is structurally recursive.

parse :: Ord tok => Parser tok r -> [ tok ] -> [ r ]
parse (xs :&: f) []      = xs
parse (xs :&: f) (c : s) = case Map.lookup c f of
  Nothing -> []
  Just f' -> parse f' s

instance Parser.Parser Parser where
  ret       = return
  p1 <*> p2 = p1 >>= \f -> p2 >>= \x -> return (f x)
  zero      = mzero
  (<|>)     = mplus
  sym       = sym
  parse     = parse
