-- There was a bug when scope checking with clauses.
module WithScopeError where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

f : Nat -> Nat
f n with y
  where y = suc n
f n | x = y x

