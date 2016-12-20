-- Andreas, 2016-12-20, issue #2349

{-# OPTIONS --show-implicit #-}

open import Agda.Primitive
open import Agda.Builtin.Equality

data D {a} {{A : Set a}} : Set a where
  c : {a : A} → D {{A}}

test : ∀ ℓ (A : Set ℓ) (x : D {{A}}) (a : A) → x ≡ c {ℓ} {{A}} {a = a}
test ℓ A x a = refl

-- ERROR:
-- x != c {{a}} of type D {{ℓ}} A
-- when checking that the expression refl has type
-- _≡_ {ℓ} {D {{ℓ}} A} x (c {{a}})

-- Note that (c {{a}}) is ill-typed here.
