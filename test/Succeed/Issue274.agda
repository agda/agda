-- The bug documented below was exposed by the fix to issue 274.

module Issue274 where

open import Common.Level

record Q a : Set (a ⊔ a) where

record R a : Set a where
  field q : Q a

  A : Set₁
  A = Set

postulate
  ℓ : Level
  r : R (ℓ ⊔ ℓ)

foo : R ℓ
foo = r

-- Issue274.agda:32,7-8
-- ℓ ⊔ ℓ !=< ℓ of type Level
-- when checking that the expression r has type R ℓ
