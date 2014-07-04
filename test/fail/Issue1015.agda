-- Andreas, 2014-03-27 fixed issue

{-# OPTIONS --copatterns --sized-types #-}

open import Common.Size

mutual
  data D (i : Size) : Set where
    inn : R i → D i

  record R (i : Size) : Set where
    inductive
    field
      force : (j : Size< i) → D j
open R

inh : (i : Size) → R i
force (inh i) j = inn (inh j)

-- inh should be rejected by termination checker

data ⊥ : Set where

elim : D ∞ → ⊥
elim (inn r) = elim (force r ∞)

absurd : ⊥
absurd = elim (inn (inh ∞))

