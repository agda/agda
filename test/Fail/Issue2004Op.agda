-- Andreas, 2024-10-08, issue #2004 (and #7533)
-- DISPLAY forms should be able to match on defined names.

open import Agda.Builtin.Equality

postulate
  A : Set
  P : A → Set
  Any : (A → Set) → (A → Set) → Set

_∈_ : A → (A → Set) → Set
x ∈ Y = Any (x ≡_) Y

{-# DISPLAY Any (_≡_ x) Y = x ∈ Y #-}

test : ∀ x Y → x ∈ Y → Any (x ≡_) Y
test x Y = Set

-- Expected error:

-- Set₁ !=< x ∈ Y → x ∈ Y
-- when checking that the expression Set has type x ∈ Y → x ∈ Y
