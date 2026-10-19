-- Andreas, 2026-09-29, issue #8780
-- Report, test case, and fix by Ulrik Buchholtz

-- master (2.9.0) --profile=modules made Agda hit __IMPOSSIBLE__ due to some race

open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_*_)
open import Agda.Builtin.Equality

-- Slow multiplication
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = go n (m * n)
  where
  go : ℕ → ℕ → ℕ
  go zero    k = k
  go (suc a) k = suc (go a k)

-- Something that takes long enough to type check to trigger the race
slow : (30 * 30) * 30 ≡ 30 * (30 * 30)
slow = refl

-- Provoke a type error
crash-by-intention : Set
crash-by-intention = zero

-- Error with --profile=modules was:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: __IMPOSSIBLE__, called at Agda/TypeChecking/Monad/Benchmark.hs:162:16

-- Expected  error: [UnequalTypes]
-- The type
--   ℕ
-- is not a subtype of
--   Set
-- when checking that the expression zero has type Set
