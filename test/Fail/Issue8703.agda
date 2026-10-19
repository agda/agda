-- A proof of False due to a bug in clause-based reduction
-- that only surfaces in call-by-need as implemented by fast reduction.

{-# OPTIONS --safe --without-K #-}
{-# OPTIONS --fast-reduce --no-call-by-name #-}  -- On by default, but supplied for clarity.
-- Both --no-fast-reduce and --call-by-name prevent the exploit.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

-- The bug only shows for an underapplied function under clause-based reduction.
-- We force evaluation of the underapplied function by passing it to
-- some other function under the call-by-need strategy.

k : (Bool → Bool) → Bool
k g = g true

f : Bool → Bool → Bool → Bool
f true x z = x
f y true = λ z → false
f false false z = z
  module M where

    -- Since we are still in the process of defining f,
    -- the original clauses are used for reduction (case tree doesn't exist yet).
    -- With call-by-need, (f true true) is evaluated.
    -- Due to underapplication, the first clause does not fire,
    -- and we skip to the next clause (faulty behavior).
    -- This results in (k (λ z → false)) which evaluates to false,
    -- making the following pass.

    lem : k (f true true) ≡ false
    lem = refl  -- Should be rejected.

-- Now with the definition of f complete and a case tree present,
-- (f true true) is evaluated correctly to (λ z → true).

later : k (f true true) ≡ true
later = refl

-- It follows that (false ≡ true).

data ⊥ : Set where

contra : {b : Bool} → b ≡ true → b ≡ false → ⊥
contra refl ()

boom : ⊥
boom = contra later (M.lem true)
