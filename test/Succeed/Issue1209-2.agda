-- A variant of code reported by Andreas Abel.

{-# OPTIONS --guardedness --sized-types #-}

open import Common.Coinduction renaming (∞ to Delay)
open import Common.Size
open import Common.Product

data ⊥ : Set where

record Stream (A : Set) : Set where
  inductive
  constructor delay
  field
    force : Delay (A × Stream A)
open Stream

head : ∀{A} → Stream A → A
head s = proj₁ (♭ (force s))

-- This type should be empty, as Stream A is isomorphic to ℕ → A.
data D : (i : Size) → Set where
  lim : ∀ i → Stream (D i) → D (↑ i)

-- Emptiness witness for D.
empty : ∀ i → D i → ⊥
empty .(↑ i) (lim i s) = empty i (head s)

-- BAD: But we can construct an inhabitant.
inh : Stream (D ∞)
inh = delay (♯ (lim ∞ inh , inh)) -- Should be rejected by termination checker.

absurd : ⊥
absurd = empty ∞ (lim ∞ inh)
