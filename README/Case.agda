------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples showing how the case expressions can be used
------------------------------------------------------------------------

module README.Case where

open import Data.Fin   hiding (pred)
open import Data.Maybe hiding (from-just)
open import Data.Nat   hiding (pred)
open import Function

-- Some simple examples.

empty : ∀ {a} {A : Set a} → Fin 0 → A
empty i = case i of λ()

pred : ℕ → ℕ
pred n = case n of λ
  { zero    → zero
  ; (suc n) → n
  }

from-just : ∀ {a} {A : Set a} (x : Maybe A) → From-just A x
from-just x = case x return From-just _ of λ
  { (just x) → x
  ; nothing  → _
  }

-- Note that some natural uses of case are rejected by the termination
-- checker:
--
-- plus : ℕ → ℕ → ℕ
-- plus m n = case m of λ
--   { zero    → n
--   ; (suc m) → suc (plus m n)
--   }
