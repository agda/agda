
module Data.Maybe where

data Maybe (a : Set) : Set where
  nothing : Maybe a
  just    : a -> Maybe a

fmap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
fmap f nothing  = nothing
fmap f (just a) = just (f a )

