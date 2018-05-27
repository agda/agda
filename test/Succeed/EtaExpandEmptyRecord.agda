open import Common.Product
open import Agda.Builtin.Equality

data ⊥ : Set where

record Empty : Set where
  field absurdity : ⊥

magic₁ : Empty → ⊥
magic₁ ()

record EmptyIrr : Set where
  field .absurdity : ⊥

magic₂ : EmptyIrr → ⊥
magic₂ ()

test : ∀ x y → magic₂ x ≡ magic₂ y
test x y = refl

postulate whatever : Set

magic₃ : Σ ⊥ (λ _ → whatever) → ⊥
magic₃ ()

magic₄ : Σ whatever (λ _ → ⊥) → ⊥
magic₄ ()

data D : whatever → Set where

magic₅ : Σ whatever D → ⊥
magic₅ ()
