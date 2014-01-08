
{-# OPTIONS --copatterns #-}

open import Common.Size

record R (i : Size) : Set where
  constructor delay
  field
    force : (j : Size< i) → R j
open R

inh : (i : Size) → R i
force (inh i) j = inh j

data ⊥ : Set where

elim : R ∞ → ⊥
elim (delay f) = elim (f ∞)

-- Gives termination error, as expected.
