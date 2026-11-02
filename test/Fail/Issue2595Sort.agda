-- Andreas, 2026-11-03, issue #2595.
-- An irrelevant argument that is only used in a sort of the codomain
-- makes the comparison of the remaining arguments heterogeneous as well:
-- the meta _ : Set lzero must not be solved by B : Set₁.

{-# OPTIONS --experimental-irrelevance #-}

open import Agda.Primitive
open import Agda.Builtin.Equality

postulate
  F : ∀ .(i : Level) → Set i → Set
  B : Set₁

test : F lzero _ ≡ F (lsuc lzero) B
test = refl
