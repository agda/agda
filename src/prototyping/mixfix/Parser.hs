------------------------------------------------------------------------
-- A parser interface
------------------------------------------------------------------------

module Parser where

infixl 4 <*>, <*, *>, <$>, <$
infixl 3 <|>

class Parser p where
  ret   :: Ord tok => r -> p tok r
  (<*>) :: Ord tok => p tok (s -> r) -> p tok s -> p tok r
  zero  :: Ord tok => p tok r
  -- /Symmetric/ choice.           
  (<|>) :: Ord tok => p tok r -> p tok r -> p tok r
  sym   :: Ord tok => tok -> p tok tok
  parse :: Ord tok => p tok r -> [tok] -> [r]

  choice :: Ord tok => [p tok r] -> p tok r
  choice = foldr (<|>) zero

  many1 :: Ord tok => p tok a -> p tok [a]
  many1 p = m
    where m = (:) <$> p <*> (ret [] <|> m)

  chainr1 :: Ord tok => p tok a -> p tok (a -> a -> a) -> p tok a
  chainr1 p op = c
    where c = (\x f -> f x) <$> p <*>
              (ret id <|> flip <$> op <*> c)

  chainl1 :: Ord tok => p tok a -> p tok (a -> a -> a) -> p tok a
  chainl1 p op = (\x f -> f x) <$> p <*> c
    where
    c =   ret (\x -> x)
      <|> (\f y g x -> g (f x y)) <$> op <*> p <*> c

(<$>) :: (Parser p, Ord tok) => (s -> r) -> p tok s -> p tok r
f <$> p = ret f <*> p

(<$) :: (Parser p, Ord tok) => s -> p tok r -> p tok s
x <$ p = const x <$> p

(<*) :: (Parser p, Ord tok) => p tok s -> p tok r -> p tok s
p1 <* p2 = const <$> p1 <*> p2

(*>) :: (Parser p, Ord tok) => p tok s -> p tok r -> p tok r
p1 *> p2 = flip const <$> p1 <*> p2

chainr3 :: (Parser p, Ord tok) => p tok a -> p tok (a -> a -> a) -> p tok a
chainr3 p op = (\x f y -> f x y) <$> p <*> op <*> chainr1 p op

chainl3 :: (Parser p, Ord tok) => p tok a -> p tok (a -> a -> a) -> p tok a
chainl3 p op = (\x f y -> f x y) <$> chainl1 p op <*> op <*> p
