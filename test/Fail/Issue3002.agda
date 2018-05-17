
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data ⊥ : Set where

data Zero : Set where
  zero : Zero

data One : Set where
  suc : Zero → One

data _≤_ : One → Zero → Set where

_≤?_ : ∀ m n → m ≤ n → ⊥
suc m ≤? zero = λ ()

thm : (f : suc zero ≤ zero → ⊥) → suc zero ≤? zero ≡ f
thm f = refl
  -- (λ ()) zero x != f x of type ⊥
  --        ^^^^
