-- Andreas, 2015-06-24

open import Common.Equality
open import Common.Product

Sing : {A : Set} (a : A) → Set
Sing a = ∃ λ b → a ≡ b

works : {A : Set} (f : ∀{a : A} → Sing a) (a : A) → Sing a
works f a = let b , p = f {_} in b , p

test : {A : Set} (f : ∀{a : A} → Sing a) (a : A) → Sing a
test f a = let b , p = f in b , p

-- ERROR WAS:
-- Type mismatch
-- when checking that the pattern b , p has type
-- {a = a₁ : .A} → Sing a₁

-- should work now
