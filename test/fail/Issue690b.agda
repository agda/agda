{-# OPTIONS --type-in-type
            --guardedness-preserving-type-constructors #-}

module Issue690b where

open import Common.Coinduction

data Rec (A : ∞ Set) : Set where
  fold : (x : ♭ A) → Rec A

infixr 4 _,_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ⊥ : Set where

{-# NON_TERMINATING #-}
D : Set
D = Rec (♯ Σ Set λ E → Σ (D ≡ E) λ _ → E → ⊥)

lam : (D → ⊥) → D
lam f = fold (D , refl , f)

app : D → D → ⊥
app (fold (.D , refl , f)) d = f d

omega : D
omega = lam (λ x → app x x)

Omega : ⊥
Omega = app omega omega
