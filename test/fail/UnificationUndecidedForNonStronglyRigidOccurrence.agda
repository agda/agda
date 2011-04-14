-- Andreas, 2011-04-14
module UnificationUndecidedForNonStronglyRigidOccurrence where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

i : (f : Nat -> Nat)(n : Nat) -> n ≡ f n -> Nat
i f n ()
-- this should fail, since n ≡ f n is not always empty, only in case of f=suc
-- thus, an occurrence does not always mean no match, only strict occurrences
-- mean that.
