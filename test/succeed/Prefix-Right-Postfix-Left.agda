open import Common.Equality
open import Common.Prelude renaming (Nat to ℕ)

infixr 4 _,_
infix  4 ,_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ

,_ : {A : Set} {B : A → Set} {x : A} → B x → Σ A B
, y = _ , y

should-be-accepted : Σ ℕ λ i → Σ ℕ λ j → Σ (i ≡ j) λ _ → Σ ℕ λ k → j ≡ k
should-be-accepted = 5 , , refl , , refl

_⊕_ : ℕ → ℕ → ℕ
_⊕_ = _+_

_↓ : ℕ → ℕ
_↓ = pred

infixl 6 _⊕_
infix  6 _↓

should-also-be-accepted : ℕ
should-also-be-accepted = 1 ⊕ 0 ↓ ⊕ 1 ↓ ⊕ 1 ⊕ 1 ↓

parses-correctly : should-also-be-accepted ≡ 1
parses-correctly = refl
