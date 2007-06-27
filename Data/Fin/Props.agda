------------------------------------------------------------------------
-- Properties related to Fin
------------------------------------------------------------------------

module Data.Fin.Props where

open import Data.Fin
open import Data.Nat

abstract

  prop-toℕ-≤ : forall {n} (x : Fin n) -> toℕ x ≤ n
  prop-toℕ-≤ fz     = z≤n
  prop-toℕ-≤ (fs i) = s≤s (prop-toℕ-≤ i)
