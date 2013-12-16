open import Common.Level

postulate
  ℓ : Level

f : (l : Level) (A : Set l) → Set ℓ
f ℓ A = A

-- Expected error:
-- ℓ != ℓ of type Level
-- (because one is a variable and one a defined identifier)
-- when checking that the expression A has type Set ℓ
