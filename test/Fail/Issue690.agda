{-# OPTIONS --type-in-type #-}
-- {-# OPTIONS -v tc.pos:10 -v tc.polarity:10 #-}
-- Andreas, 2012-09-06, message on Agda list "Forget Hurken's paradox..."

module Issue690 where

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ⊥ : Set where

data D : Set where
  abs : ∀ {E : Set} → D ≡ E → (E → ⊥) → D

lam : (D → ⊥) → D
lam f = abs refl f

app : D → D → ⊥
app (abs refl f) d = f d

omega : D
omega = lam (λ x → app x x)

Omega : ⊥
Omega = app omega omega

