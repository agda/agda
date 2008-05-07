------------------------------------------------------------------------
-- A parser interface
------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             Rank2Types #-}

module Parser where

import Control.Applicative
import Data.Foldable
import IndexedOrd

class (Eq tok, Alternative p, Monad p) => Parser p tok | p -> tok where
  symbol :: p tok

sym :: Parser p tok => tok -> p tok
sym c = do
  c' <- symbol
  if c == c' then return c' else empty

choice :: Parser p tok => [p r] -> p r
choice = asum

many1 :: Parser p tok => p a -> p [a]
many1 = some

chainr1 :: Parser p tok => p a -> p (a -> a -> a) -> p a
chainr1 p op = c
  where c = (\x f -> f x) <$> p <*>
            (pure id <|> flip <$> op <*> c)

chainl1 :: Parser p tok => p a -> p (a -> a -> a) -> p a
chainl1 p op = (\x f -> f x) <$> p <*> c
  where
  c =   pure (\x -> x)
    <|> (\f y g x -> g (f x y)) <$> op <*> p <*> c

chainr3 :: Parser p tok => p a -> p (a -> a -> a) -> p a
chainr3 p op = (\x f y -> f x y) <$> p <*> op <*> chainr1 p op

chainl3 :: Parser p tok => p a -> p (a -> a -> a) -> p a
chainl3 p op = (\x f y -> f x y) <$> chainl1 p op <*> op <*> p

-- • `between` [x, y, z] ≈ x • y • z.

between :: Parser p tok => p a -> [tok] -> p [a]
p `between` []       = empty
p `between` [x]      = [] <$ sym x
p `between` (x : xs) = (:) <$> (sym x *> p) <*> (p `between` xs)

class Parser p tok => NTParser p nt tok | p -> tok nt where
  -- | Parser for the given non-terminal.
  nonTerm :: nt r -> p r

-- | A \"grammar\": a mapping from non-terminals to right-hand sides
-- (parsers).

type Grammar p nt = forall r. nt r -> p r
