-- A variant of code reported by Andreas Abel.

{-# OPTIONS --guardedness --sized-types #-}

open import Agda.Builtin.Size

data ⊥ : Set where

mutual
  data D : Size → Set where
    inn : ∀ i → D' i → D (↑ i)

  record D' (i : Size) : Set where
    coinductive
    constructor ♯
    field ♭   : D i
open D'


iter : ∀{i} → D i → ⊥
iter (inn i t) = iter (♭ t)

-- Should be rejected by termination checker
bla : D' ∞
♭ bla = inn ∞ bla

false : ⊥
false = iter (♭ bla)
