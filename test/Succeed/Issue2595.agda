-- Andreas, 2026-10-30, issue #2595.
-- Heterogeneous comparisons after a shape-irrelevantly used
-- irrelevant argument still work when no metas are involved.

{-# OPTIONS --experimental-irrelevance #-}

open import Agda.Builtin.Equality

data Bool : Set where
  true false : Bool

data IsTrue : ..(x : Bool) → Set where
  tt : IsTrue true

postulate
  H : ∀ .x (z : IsTrue x) → Set
  f : ∀ .x → IsTrue x

-- f x : IsTrue x and f y : IsTrue y are compared heterogeneously.

test : ∀ x y → H x (f x) ≡ H y (f y)
test x y = refl

-- Metas can still be solved if the solution has the right type.

test-meta : H true (f true) ≡ H true _
test-meta = refl
