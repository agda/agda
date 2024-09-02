-- Andreas, 2024-07-19, PR #7379
-- Trigger error NeedOptionUniversePolymorphism

{-# OPTIONS --no-universe-polymorphism #-}

open import Agda.Primitive renaming (Set to Type)

postulate
  A : Type 1

-- Expected error:
-- Universe polymorphism is disabled
-- (use option --universe-polymorphism to allow level arguments to sorts)
-- when checking that the expression Type 1 is a type
