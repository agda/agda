-- Andreas, 2023-08-05, test primary motivation for Propω.
-- The example put forward in #3437 now needs --large-indices.

{-# OPTIONS --prop --large-indices #-}

module _ where

open Agda.Primitive

module Explicit where

  -- Lists of elements of types at any finite level.

  data HList : Setω where
    hnil  : HList
    hcons : (ℓ : Level) (A : Set ℓ) → A → HList → HList

  -- Predicate stating that all elements satisfy a given property.

  data All (P : (ℓ : Level) (A : Set ℓ) → A → Prop ℓ) : HList → Propω where
    anil  : All P hnil
    acons : (ℓ : Level) (A : Set ℓ) (x : A) (xs : HList)
          → P ℓ A x → All P xs → All P (hcons ℓ A x xs)

    -- Since the sorts of Level and Set ℓ do not fit into Propω,
    -- we need --large-indices.

module Implicit where

  variable
    ℓ : Level
    A : Set ℓ

  -- Lists of elements of types at any finite level.

  data HList : Setω where
    []  : HList
    _∷_ : A → HList → HList

  variable
    x  : A
    xs : HList

  -- Predicate stating that all elements satisfy a given property.

  data All (P : ∀{ℓ} {A : Set ℓ} → A → Prop ℓ) : HList → Propω where
    []  : All P []
    _∷_ : P x → All P xs → All P (x ∷ xs)
