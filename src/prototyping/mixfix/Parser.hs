------------------------------------------------------------------------
-- A parser interface
------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             Rank2Types #-}

module Parser where

import Control.Applicative

import IndexedOrd

class (Alternative p, Monad p) => Parser p tok | p -> tok where
  symbol :: p tok

  parse :: p r -> [ tok ] -> [ r ]

sat :: Parser p tok => (tok -> Bool) -> p tok
sat p = do
  c <- symbol
  if p c then return c else empty

sym :: Eq tok => Parser p tok => tok -> p tok
sym c = sat (== c)

sepBy :: Parser p tok => p r -> p sep -> p [r]
p `sepBy` sep = (:) <$> p <*> many (sep *> p)

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

-- | • `between` [x, y, z] ≈ x • y • z.

between :: Parser p tok => p a -> [p b] -> p [a]
p `between` []       = empty
p `between` [x]      = [] <$ x
p `between` (x : xs) = (:) <$> (x *> p) <*> (p `between` xs)

class Parser p tok => NTParser p nt tok | p -> tok nt where
  -- | Parser for the given non-terminal.
  nonTerm :: IndexedOrd nt => nt r -> p r

  parseWithGrammar :: Grammar p nt -> p r -> [ tok ] -> [ r ]

-- | A \"grammar\": a mapping from non-terminals to right-hand sides
-- (parsers).

type Grammar p nt = forall r. nt r -> p r
