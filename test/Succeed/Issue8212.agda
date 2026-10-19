-- Issue 2025-11-19, issue #8212, reported by nad

open import Agda.Builtin.Equality

postulate
  magic : (A : Set) (x y : A) → x ≡ y

module OP where

  module M (_ : Set₁) where

    data D₁ : Set where
      c₁ : D₁

  open M Set

  mutual
    data D₂ (x : D₁) : Set where
      c₂₁ : D₂ x
      c₂₂ : (y : D₃ x) → D₄ x y → D₂ x

    data D₃ (x : D₁) : Set where
      c₃ : D₂ x → D₃ x → D₃ x

    f : (x : D₁) → D₃ x → D₃ x
    f x (c₃ y z) = c₃ y z

    g : (x : D₁) → D₃ x → D₃ x
    g x y = c₃ c₂₁ (f x y)

    data D₄ (x : D₁) : D₃ x → Set where
      c₄ : (y z : D₃ x) → y ≡ g x z → D₄ x y

  mutual

    h₁ : D₂ c₁ → D₂ c₁
    h₁ c₂₁       = c₂₁
    h₁ (c₂₂ x y) = c₂₂ (h₂ x) (h₃ x y)

    h₂ : D₃ c₁ → D₃ c₁
    h₂ (c₃ x y) = c₃ (h₁ x) (h₂ y)

    h₃ : (x : D₃ c₁) → D₄ c₁ x → D₄ c₁ (h₂ x)
    h₃ _ (c₄ x y z) = c₄ (h₂ x) (h₂ y) (h₄ x y z)

    h₄ : (x y : D₃ c₁) → x ≡ g c₁ y → h₂ x ≡ g c₁ (h₂ y)
    h₄ .(c₃ c₂₁ (f c₁ x)) x refl =
             -- ^^^^^^^^
      magic (D₃ c₁) (c₃ c₂₁ (h₂ (f c₁ x))) (c₃ c₂₁ (f c₁ (h₂ x)))
                             -- ^^^^^^^^

  -- This termination checks on Agda 2.8.0 and should continue to termination check
  -- It uses the subterm ordering (se ^^^) and dot-pattern termination.


-- The following variant introduces an alias for a constructor
-- which should not upset the subterm ordering.
-- It did not pass on Agda-2.8.0 but passes now.

module VariantWithAlias where

  module M (_ : Set₁) where

    data D₁ : Set where
      c₁' : D₁

  open M Set

  -- This definition makes dot-pattern termination
  -- succeed on current master (2025-11-19)
  -- but fail on Agda-2.8.0.

  c₁ : D₁
  c₁ = c₁'

  mutual
    data D₂ (x : D₁) : Set where
      c₂₁ : D₂ x
      c₂₂ : (y : D₃ x) → D₄ x y → D₂ x

    data D₃ (x : D₁) : Set where
      c₃ : D₂ x → D₃ x → D₃ x

    f : (x : D₁) → D₃ x → D₃ x
    f x (c₃ y z) = c₃ y z

    g : (x : D₁) → D₃ x → D₃ x
    g x y = c₃ c₂₁ (f x y)

    data D₄ (x : D₁) : D₃ x → Set where
      c₄ : (y z : D₃ x) → y ≡ g x z → D₄ x y

  mutual

    h₁ : D₂ c₁ → D₂ c₁
    h₁ c₂₁       = c₂₁
    h₁ (c₂₂ x y) = c₂₂ (h₂ x) (h₃ x y)

    h₂ : D₃ c₁ → D₃ c₁
    h₂ (c₃ x y) = c₃ (h₁ x) (h₂ y)

    h₃ : (x : D₃ c₁) → D₄ c₁ x → D₄ c₁ (h₂ x)
    h₃ _ (c₄ x y z) = c₄ (h₂ x) (h₂ y) (h₄ x y z)

    h₄ : (x y : D₃ c₁) → x ≡ g c₁ y → h₂ x ≡ g c₁ (h₂ y)
    h₄ .(c₃ c₂₁ (f c₁ x)) x refl =
      magic (D₃ c₁) (c₃ c₂₁ (h₂ (f c₁ x))) (c₃ c₂₁ (f c₁ (h₂ x)))
