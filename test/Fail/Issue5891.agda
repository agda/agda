-- AIM XXXV, 2022-05-06, issue #5891:
-- SizeUniv : SizeUniv was causing non-termination and inhabitation of Size< 0.
-- This is inconsistent; proof by Jonathan Chan.

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

-- Step 1: Hurken's Paradox with SizeUniv : SizeUniv.

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

-- Prevent unfolding, as this term has no whnf.
-- Stops Agda from looping.

abstract
  false : False
  false = L R

-- This gives us a predecessor on Size.

size-pred : ∀ i → Size< i
size-pred i = false (Size< i)

-- Step 2: Size predecessor is inconsistent.

-- Jonathan Chan:
-- I managed to do so using ∞ but only because it's the only closed
-- size expression, not using the ∞ < ∞ property, although the
-- principle is the same as for #3026:

data _>_ (s : Size) : Size → Set where
  lt : (r : Size< s) → s > r

data Acc (s : Size) : Set where
  acc : (∀ {r} → s > r → Acc r) → Acc s

wf : ∀ s → Acc s
wf s = acc λ{ (lt r) → wf r }

¬wf : ∀ s → Acc s → ⊥
¬wf s (acc p) = ¬wf (size-pred s) (p (lt (size-pred s)))

absurd : ⊥
absurd = (¬wf ∞) (wf ∞)
