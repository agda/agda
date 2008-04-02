------------------------------------------------------------------------
-- An elegant but very slow variant of AmbTrie
------------------------------------------------------------------------

-- I think that the code below would be accepted directly by Coq's
-- termination and productivity checkers (if written in Coq style,
-- with Parser declared as being coinductive).

-- Note that this parser does not do any on-the-fly left
-- factorisation.

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module SlowParser where

import Control.Monad
import qualified Parser
import Control.Applicative

infix 4 :&:

data Parser tok r = [ r ] :&: (tok -> Parser tok r)

-- Note that empty and (<|>) are productive. (If we assume a total language.)

instance Ord tok => Alternative (Parser tok) where
  empty                     = [] :&: const empty
  xs1 :&: f1 <|> xs2 :&: f2 = xs1 ++ xs2 :&: (\c -> f1 c <|> f2 c)

-- Note that bind is productive.

instance Ord tok => Monad (Parser tok) where
  return x       = [x] :&: const empty
  xs :&: f >>= g = foldr (<|>) ([] :&: (\c -> f c >>= g)) (map g xs)

instance Ord tok => Applicative (Parser tok) where
  pure      = return
  p1 <*> p2 = p1 >>= \f -> p2 >>= \x -> return (f x)

instance Ord tok => Functor (Parser tok) where
  fmap = liftM

-- Note that parse is structurally recursive.

parse :: Ord tok => Parser tok r -> [ tok ] -> [ r ]
parse (xs :&: f) []      = xs
parse (xs :&: f) (c : s) = parse (f c) s

instance Ord tok => Parser.Parser (Parser tok) tok where
  sym c = [] :&: \c' -> if c == c' then return c' else empty
  parse = parse
