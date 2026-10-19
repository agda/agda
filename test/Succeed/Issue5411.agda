-- Andreas, 2026-04-30, issue #5411, duplicate of #6770

open import Agda.Primitive

module _ (Sort : Set) (Foo : Set) where

record Setoid ℓ : Set (lsuc ℓ) where
  field Carrier : Set ℓ

record SetoidModel ℓ : Set (lsuc ℓ) where
  field Den : Sort → Setoid ℓ

variable
  ℓ : Level  -- necessary

module Works (M : SetoidModel ℓ) where
  open SetoidModel M
  postulate works : ∀ s → Den s .Setoid.Carrier

module Test (M : SetoidModel ℓ) (open SetoidModel M) where
  postulate test : ∀ s → Den s .Setoid.Carrier

-- (Foo → Setoid (ℓ _24)) !=< Setoid _ℓ_23
-- when checking that the inferred type of an application
--   Foo → Setoid (ℓ _24)
-- matches the expected type
--   Setoid _ℓ_23
