-- A variant of code reported by Andreas Abel (who suggested that this
-- way to trigger the bug might have been due to NAD).

{-# OPTIONS --guardedness --sized-types #-}

open import Agda.Builtin.Sigma
open import Agda.Builtin.Size

data ⊥ : Set where

record Delay (A : Set) : Set where
  coinductive
  constructor ♯
  field ♭   : Σ A λ _ → ⊥ → Delay A
  -- Recursive in order to please the termination checker.

open Delay

data D : Size → Set where
  inn : ∀ i → Delay (D i) → D (↑ i)

iter : ∀{i} → D i → ⊥
iter (inn i t) = iter (fst (♭ t))

-- Should be rejected by the termination checker.

bla : Delay (D ∞)
♭ bla = inn ∞ bla , λ()

false : ⊥
false = iter (fst (♭ bla))
