module Negative5 where

data Funny (A : Set) : Set where
  funny : A -> Funny (Funny A -> A) -> Funny A

