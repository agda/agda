-- Andreas, 2026-10-03, issue #8783
-- Mimer should also use functions mutually defined with the current one.

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

data D (b : Bool) : Set where

data E (b : Bool) : Set where
  wrap : D b → E b

mutual
  castD : D true → D false
  castD = λ ()

  castE : E true → E false
  castE (wrap x) = {!!}
    -- Expected: wrap (castD x)

-- The structurally smaller argument may go to a different position.

mutual
  castD' : D true → Nat → D false
  castD' = λ ()

  castE' : Nat → E true → E false
  castE' n (wrap x) = {!!}
    -- Expected: wrap (castD' x n) or similar
