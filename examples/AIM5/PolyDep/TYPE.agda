module TYPE where
data Pair (a b : Set1) : Set1 where
  pair : a -> b -> Pair a b

data Unit : Set1 where
  unit : Unit


