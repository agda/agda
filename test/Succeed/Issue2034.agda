
module _ where

open import Agda.Builtin.Nat

postulate
  T : Set

  C₁ : Set
  instance I₁ : C₁

  C₂ : Nat → Set
  instance I₂ : ∀ {n} → C₂ n

it : {A : Set} {{_ : A}} → A
it {{x}} = x

postulate
  f₁ : {{_ : {_ : Nat} → C₁}} → T
  f₂ : {{_ : ∀ {n} → C₂ n}} → T

works₁ : T
works₁ = f₁         -- f₁ {{λ _ → I₁}}

fails₁ : T
fails₁ = f₁ {{it}}  -- internal error

works₂ : T
works₂ = f₂         -- f₂ {{λ n → I₂ {n}}}

fails₂ : T
fails₂ = f₂ {{it}}  -- internal error
