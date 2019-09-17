open import Common.Level

postulate
  ℓ : Level

f : (l : Level) (A : Set l) → Set ℓ
f ℓ A = A

-- Expected error:
-- ℓ != ℓ of type Level
-- (because one is a variable and one a defined identifier)
-- when checking that the expression A has type Set ℓ

-- Jesper, 2018-12-10, New error:
-- ℓ != Issue998a.ℓ of type Level
-- when checking that the expression A has type Set ℓ

-- Jesper, 2019-09-16, new error:
-- Set ℓ != Set Issue998d.ℓ
-- when checking that the expression A has type Set ℓ
