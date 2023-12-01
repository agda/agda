-- Andreas, 2023-10-23, issue #6913, testcase and fix by Jonathan Chan
-- Was an internal error in Constraints.hs (Agda 2.6.4)..

{-# OPTIONS --guarded #-}

primitive primLockUniv : Set₁

variable κ₀ : primLockUniv
postulate ✓ : κ₀

force : {P : primLockUniv → Set} → (∀ κ → (@tick t : κ) → (P κ)) → (∀ κ → P κ)
force f κ = f κ ✓

-- Expected error:

-- The term ✓, given as an argument to the guarded value
--   f κ : κ → P κ
-- can not be used as a @tick argument, since it does not mention any @tick variables.
-- when checking that the expression f κ ✓ has type P κ
