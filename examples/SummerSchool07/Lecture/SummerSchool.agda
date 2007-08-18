
module SummerSchool where

{-

Lecture:

- General introduction (slides)
- Basic datatypes and functions
- Some Curry-Howard stuff
- Inductive families (what?)

-}

-- A simple datatype

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

-- Curry Howard

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

-- Dependent types

