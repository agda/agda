{-# OPTIONS --allow-unsolved-metas #-}
module _ where

open import Agda.Primitive
open import Agda.Builtin.Nat

module Test₁ where

  record ⊤ {a} : Set a where
    constructor tt

  data G : (A : Set) → ⊤ {_} → Set where
    d : (x : ⊤) → G ⊤ x

  test : (g : G ⊤ tt) → Set
  test (d x) = ⊤

module Test₂ where

  postulate A : Set
            a : A

  record R {a} : Set a where
    constructor mkR
    field x : A

  data G : (A : Set) → R {_} → Set where
    d : (x : R) → G R x

  test : (g : G R (mkR a)) → R
  test (d x) = x

module Test₃ where

  postulate A : Set
            a : A

  record R {a} : Set a where
    constructor mkR
    field x y : A

  data G : (A : Set) → R {_} → Set where
    d : (x : R) → G R x

  -- Forced: mkR x y
  test₁ : ∀ x y → (g : G R (mkR x y)) → Set
  test₁ x y (d (mkR x y)) = A

  -- .(mkR x y) turns into z with x = .(R.x z) and y = .(R.y z)
  test₂ : ∀ x y → (g : G R (mkR x y)) → Set
  test₂ x y (d .(mkR x y)) = A

  test₃ : ∀ x y → (g : G R (mkR x y)) → Set
  test₃ .(R.x z) .(R.y z) (d z) = A
