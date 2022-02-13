-- This test case seems to be due to Andreas Abel, Andrea Vezzosi and
-- NAD. The code below should be rejected.

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

data SizeLt (i : Size) : Set where
  size : (j : Size< i) → SizeLt i

-- Legal again in 2.5.1
getSize : ∀{i} → SizeLt i → Size
getSize (size j) = j

-- Structurally inductive (c), coinductive via sizes.
data U (i : Size) : Set where
  c : ((s : SizeLt i) → U (getSize s)) → U i

data ⊥ : Set where

empty : U ∞ → ⊥
empty (c f) = empty (f (size ∞))  -- f x <= f < c f

-- If U is a data type this should not be possible:
inh : ∀ i → U i
inh i = c λ{ (size j) → inh j }

absurd : ⊥
absurd = empty (inh ∞)
