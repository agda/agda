module Subset where

data Subset (A : Set) (P : A -> Set) : Set where
  inn : (a : A) -> .(P a) -> Subset A P

out : forall {A P} -> Subset A P -> A
out (inn a p) = a

