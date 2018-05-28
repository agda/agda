
-- See also issues 1159 and 480.

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

case_of_ : {A B : Set} → A → (A → B) → B
case x of f = f x

-- correctError : Bool → Bool
-- correctError = \
--   { true  → 1        -- error is here and reported here
--   ; false → true
--   }

test : Bool → Bool
test b = case b of \
  { true  → 0        -- error is here
  ; false → false    -- but is reported here
  }

-- Should report error at the 0, not at the false.
