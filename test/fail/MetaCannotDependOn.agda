
module MetaCannotDependOn where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

postulate
  Vec : Nat -> Set -> Set
  f : (A : Set) -> ((n : Nat) -> A -> Vec n Nat) -> Nat

err : Nat
err = f _ (\ n xs -> xs)

