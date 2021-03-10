open import Agda.Builtin.Size

record R (A : Size → Set) (i : Size) : Set where
  field
    force : (j : Size< i) → A j

data D (A : Size → Set) (i : Size) : Set where
  c : R A i → D A i

postulate
  P : (A : Size → Set) → D A ∞ → D A ∞ → Set

F : (Size → Set) → Set
F A = (x : A ∞) (y : D A ∞) →
      P _ (c (record { force = λ j → x })) y

-- WAS:
-- x != ∞ of type Size
-- when checking that the expression y has type D (λ _ → A ∞) ∞

-- SHOULD BE:
-- x₁ != ∞ of type Size
-- when checking that the expression y has type D (λ _ → A ∞) ∞
