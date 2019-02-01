-- A variant of code reported by Andreas Abel.

{-# OPTIONS --guardedness --sized-types #-}

open import Agda.Builtin.Size

data ⊥ : Set where

mutual
  data D (i : Size) : Set where
    inn : D' i → D i

  record D' (i : Size) : Set where
    coinductive
    field ♭   : {j : Size< i} → D j
open D'

bla : ∀{i} → D' i
♭ bla = inn bla

-- Should be rejected by termination checker
iter : D ∞ → ⊥
iter (inn t) = iter (♭ t)

false : ⊥
false = iter (♭ bla)
