module StronglyRigidOccurrence where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

test : let X : Nat; X = _ in X ≡ suc X
test = refl
-- this gives an error in the occurs checker