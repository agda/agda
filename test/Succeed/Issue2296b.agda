
postulate
  A : Set
  a : A

data D : Set where
  d : D

data E : Set where
  e₀ : E
  e₁ : E → E
  e₂ : E → E → E

_[_] : E → E → E
e₀       [ y ] = y
e₁ x     [ y ] = e₁ x
e₂ x₁ x₂ [ y ] = e₂ (x₁ [ y ]) (x₂ [ y ])

data P : E → Set where
  p₁ : ∀ x₁ x₂ → P x₁ → P x₂ → P (e₂ x₁ x₂)
  p₂ : ∀ x → P (x [ e₁ x ]) → P (e₁ x)
  p₃ : ∀ x → P (e₁ x)

module M (_ : A) where

  record R (A B : Set) : Set where
    field f : A → B

  instance
    r₁ : R D D
    R.f r₁ d = d

open M a

open R ⦃ … ⦄ public

r₂ : R D E
R.f r₂ d = e₀

instance

  r₃ : {A : Set} ⦃ c : R A D ⦄ → R A E
  R.f (r₃ ⦃ c ⦄) x = R.f r₂ (R.f c x)

f′ : {A : Set} ⦃ c : R A D ⦄ → A → E
f′ = f

postulate
  p : {A : Set} ⦃ c : R A D ⦄ (x : A) → P (f′ x)

rejected : P (e₂ (e₁ e₀) (f d))
rejected = p₁ _ (f′ d) (p₂ _ (p₃ e₀)) (p d)
