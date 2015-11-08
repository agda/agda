-- You can use _ in a binding position in notation.
module WildcardNotation where

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : ∀ x → B x → Σ A B

syntax Σ A (λ _ → B) = A × B

swap : ∀ {A B} → A × B → B × A
swap (x , y) = y , x

syntax compose (λ _ → x) (λ _ → y) = x instead-of y
compose : {A B C : Set} → (B → C) → (A → B) → (A → C)
compose f g = λ x → f (g x)

open import Common.Prelude
open import Common.Equality

thm₁ : swap (1 , 2) ≡ (2 , 1)
thm₁ = refl

thm₂ : (a b : Nat) → (5 instead-of a) b ≡ 5
thm₂ a b = refl
