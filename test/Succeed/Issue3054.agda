-- Andreas, 2026-05-09, issue #3054, regression in 2.6.0 introduced by fix of #2964
-- Reported and test case by Andrea Vezzosi

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool

T : Bool → Set
T true  = Bool → Bool
T false = Bool → Bool

foo : Σ (∀ b → T b) (\ f → ∀ x → f false x ≡ true)
foo .fst true  false = true  -- This split was making clause 3 non-definitional, but not rightfully so.
foo .fst true  true  = true
foo .fst false x     = true  -- This clause should be a definitional equality even during lhs checking.
-- the following should pass.
-- we can give the "refl", but after reloading it fails.
foo .snd x           = refl

-- Should succeed
