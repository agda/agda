-- {-# OPTIONS -v tc.proj.like:30 #-}

open import Common.Bool
open import Common.Equality

abstract
  Id : Set → Set
  Id A = A

f : ∀ A → Id A → Id A
f A x = x
{-# NOINLINE f #-}

postulate
  foo : ∀{X : Set} (x y : X) → x ≡ y → Set

abstract
  bla : Set
  bla = foo (f Bool true) false refl

-- WAS:
-- true != false of type Bool
-- when checking that the expression refl has type f _ true ≡ false

-- EXPECTED:
-- true != false of type Bool
-- when checking that the expression refl has type f Bool true ≡ false
