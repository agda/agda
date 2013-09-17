module Issue848 where

A : Set1
A = B module _ where
  B : Set1
  B = Set

C : Set1
C = B


D : Set1
D = E module _ where
  E : Set1
  E = Set


F : Set1
F = G module _ where
  G : Set1
  G = H module _ where
    H : Set1
    H = Set
