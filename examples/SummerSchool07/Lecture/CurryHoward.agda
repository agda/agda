
module CurryHoward where

-- Propositions as types!

data True : Set where
  tt : True

data False : Set where

data _∧_ (P Q : Set) : Set where
  _,_ : P -> Q -> P ∧ Q

data _∨_ (P Q : Set) : Set where
  inl : P -> P ∨ Q
  inr : Q -> P ∨ Q

data ∃ (A : Set)(P : A -> Set) : Set where
  ex : (x : A) -> P x -> ∃ A P

¬_ : Set -> Set
¬ A = A -> False

∀ : (A : Set)(P : A -> Set) -> Set
∀ A P = (x : A) -> P x

-- Some simple examples

swap : {P Q : Set} -> P ∧ Q -> Q ∧ P
swap (p , q) = (q , p)

notNotEM : (P : Set) -> ¬ ¬ (P ∨ ¬ P)
notNotEM P = {! !}
