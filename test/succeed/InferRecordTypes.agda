-- We can infer the type of a record by comparing the given
-- fields against the fields of the currently known records.
module InferRecordTypes where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

record _×_ (A B : Set) : Set where
  field
    fst : A
    snd : B

pair = record { fst = zero; snd = zero }

record R₁ : Set where
  field
    x₁ : Nat

r₁ = record { x₁ = zero }

data T {A : Set} : A → Set where
  mkT : ∀ n → T n

record R₂ A : Set where
  field
    {x₁} : A
    x₂   : T x₁

r₂ = record { x₂ = mkT (suc zero) }

record R₃ : Set where
  field
    x₁ x₃ : Nat

r₃ = record { x₁ = zero; x₃ = suc zero }