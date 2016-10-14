-- Andreas, 2016-10-12 AIM XXIV, issue #2256

open import Common.Equality

module _ a (A : Set a) where

data ⊥ : Set where

abs : ⊥ → Set a
abs = λ()

test : (x : ⊥) → abs x ≡ A
test x = refl

-- ERROR WAS:
-- (λ ()) a A x != A of type Set a
-- when checking that the expression refl has type abs x ≡ A

-- EXPECTED:
-- (λ ()) x != A of type Set a
-- when checking that the expression refl has type abs x ≡ A
