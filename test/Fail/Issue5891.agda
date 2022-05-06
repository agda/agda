-- AIM XXXV, 2022-05-06, issue #5891:
-- SizeUniv : SizeUniv was causing non-termination and inhabitation of Size< 0.

{-# OPTIONS --sized-types #-}

open import Agda.Primitive
open import Agda.Builtin.Size

data ⊥ : Set where

-- Original exploit:
-- data False : SizeUniv where

False : SizeUniv
False = (X : SizeUniv) → X

-- Should fail.

-- Expected error:
-- Setω != SizeUniv
-- when checking that the expression (X : SizeUniv) → X has type SizeUniv


℘ : SizeUniv → SizeUniv
℘ S = S → SizeUniv

U : SizeUniv
U = ∀ (X : SizeUniv) → (℘ (℘ X) → X) → ℘ (℘ X)

τ : ℘ (℘ U) → U
τ t = λ X f p → t (λ x → p (f (x X f)))

σ : U → ℘ (℘ U)
σ s = s U τ

Δ : ℘ U
Δ y = (∀ p → σ y p → p (τ (σ y))) → False

Ω : U
Ω = τ (λ p → (∀ x → σ x p → p x))

R : ∀ p → (∀ x → σ x p → p x) → p Ω
R _ 𝟙 = 𝟙 Ω (λ x → 𝟙 (τ (σ x)))

M : ∀ x → σ x Δ → Δ x
M _ 𝟚 𝟛 = 𝟛 Δ 𝟚 (λ p → 𝟛 (λ y → p (τ (σ y))))

L : (∀ p → (∀ x → σ x p → p x) → p Ω) → False
L 𝟘 = 𝟘 Δ M (λ p → 𝟘 (λ y → p (τ (σ y))))

false : False
false = L R

not-true : ∀ i → Size< i
not-true i = false (Size< i)

data Empty (i : Size) : Set where
  emp : ∀{j : Size< i} → Empty j → Empty i

empty : ∀ i → Empty i
empty i = empty (false (Size< i))

{-

-- -}


-- data Eq {ℓ} (A : Set ℓ) (x : A) : A → Set ℓ where
--   refl : Eq A x x

-- -}
-- -}
-- -}
-- -}
