-- A minor variant of code reported by Andreas Abel. The code below
-- should be rejected.

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

data ⊥ : Set where

data SizeLt (i : Size) : Set where
  size : (j : Size< i) → SizeLt i

<∞ : SizeLt ∞
<∞ = size ∞

data D (i : Size) : SizeLt i → Set where
  c : ∀ {i' : Size< i} → ((j : SizeLt i') → D i' j) → D i (size i')

f : D ∞ <∞ → ⊥
f (c h) = f (h <∞)

d : ∀ i s → D i s
d i (size j) = c (d j)

loop : ⊥
loop = f (d ∞ <∞)
