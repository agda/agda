module Issue599 where

data Bool : Set where
  true false : Bool

-- standard lambda here
foo : Bool → Bool
foo = ?

-- pattern matching lambda here
bar : Bool → Bool
bar = ?

