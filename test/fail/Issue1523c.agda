-- Andreas, 2015-05-28

open import Common.Size

fix : ∀ {C : Size → Set} → (∀ i → (∀ (j : Size< i) → C j) → C i) → ∀ i → C i
fix t i = t i λ (j : Size< i) → fix t j
-- Expected error:
-- Possibly empty type of sizes  (Size< i)
-- when checking that the expression λ (j : Size< i) → fix t j has
-- type (j : Size< i) → .C j
