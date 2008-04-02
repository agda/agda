------------------------------------------------------------------------
-- A parser interface
------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module Parser where

import Control.Applicative
import Data.Foldable

class (Alternative p, Ord tok) => Parser p tok | p -> tok where
  sym   :: tok -> p tok
  parse :: p r -> [tok] -> [r]

  choice :: [p r] -> p r
  choice = asum

  many1 :: p a -> p [a]
  many1 = some

  chainr1 :: p a -> p (a -> a -> a) -> p a
  chainr1 p op = c
    where c = (\x f -> f x) <$> p <*>
              (pure id <|> flip <$> op <*> c)

  chainl1 :: p a -> p (a -> a -> a) -> p a
  chainl1 p op = (\x f -> f x) <$> p <*> c
    where
    c =   pure (\x -> x)
      <|> (\f y g x -> g (f x y)) <$> op <*> p <*> c

chainr3 :: Parser p tok => p a -> p (a -> a -> a) -> p a
chainr3 p op = (\x f y -> f x y) <$> p <*> op <*> chainr1 p op

chainl3 :: Parser p tok => p a -> p (a -> a -> a) -> p a
chainl3 p op = (\x f y -> f x y) <$> chainl1 p op <*> op <*> p
