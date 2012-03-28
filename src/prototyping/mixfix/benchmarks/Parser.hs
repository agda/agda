------------------------------------------------------------------------
-- A parser interface
------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module Parser where

import Control.Applicative
import Data.Foldable

class Alternative p => Parser p k r' tok
      | p -> tok, p -> k, p -> r' where
  sym :: Eq tok => tok -> p tok

  -- | The user must annotate every memoised parser with a /unique/
  -- key. (Parameterised parsers need separate keys for separate
  -- inputs.)

  memoise :: (Ord k, Ord r') => k -> p r' -> p r'
  memoise _ p = p

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

chainr3 :: Parser p k r' tok => p a -> p (a -> a -> a) -> p a
chainr3 p op = (\x f y -> f x y) <$> p <*> op <*> chainr1 p op

chainl3 :: Parser p k r' tok => p a -> p (a -> a -> a) -> p a
chainl3 p op = (\x f y -> f x y) <$> chainl1 p op <*> op <*> p

-- • `between` [x, y, z] ≈ x • y • z.

between :: (Parser p k r' tok, Eq tok) => p a -> [tok] -> p [a]
p `between` []       = empty
p `between` [x]      = [] <$ sym x
p `between` (x : xs) = (:) <$> (sym x *> p) <*> (p `between` xs)
