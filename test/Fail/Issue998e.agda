open import Common.Level

postulate
  ℓ : Level

data D : Set (lsuc ℓ) where
  c : (ℓ : Level) → Set ℓ → D

-- Bad error:
-- The type of the constructor does not fit in the sort of the
-- datatype, since Set (lsuc ℓ) is not less or equal than Set (lsuc ℓ)
-- when checking the constructor c in the declaration of D

-- Jesper, 2018-12-09: new, better error:
-- Set (lsuc ℓ₁) is not less or equal than Set (lsuc ℓ)
-- when checking that the type (ℓ₁ : Level) → Set ℓ₁ → D of the
-- constructor c fits in the sort Set (lsuc ℓ) of the datatype.
