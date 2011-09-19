------------------------------------------------------------------------
-- The Agda standard library
--
-- An example showing how the case expression can be used
------------------------------------------------------------------------

module README.Case where

-- Natural numbers.

open import Data.Nat hiding (pred)
open import Function

-- A stupid example.

pred : ℕ → ℕ
pred n = case n return (λ _ → ℕ) of λ
  { zero    → zero
  ; (suc n) → n
  }

-- Note that some natural uses of case are rejected by the termination
-- checker:
--
-- plus : ℕ → ℕ → ℕ
-- plus m n = case m return (λ _ → ℕ) of λ
--   { zero    → n
--   ; (suc m) → suc (plus m n)
--   }
