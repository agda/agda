-- Andreas, 2017-10-04, issue #2765, reported by nad
-- Problem: inferred level expressions are often "reversed"

open import Agda.Primitive

postulate
  F : (ℓ : Level) → Set ℓ

G : (a b c : Level) → Set {!!}  -- C-c C-=
G a b c = F a → F b → F c

-- WAS:
-- ?0 := c ⊔ (b ⊔ a)

-- Expected: Inferred level should be
-- ?0 := a ⊔ (b ⊔ c)
