{-# OPTIONS --allow-unsolved-metas #-}
module Issue107 where

data Bool : Set where
  true : Bool
  false : Bool

data False : Set where
record True : Set where

T : Bool -> Set
T false = False
T _  = True

foo : ((a : Bool) -> T a) -> True
foo f = f _
