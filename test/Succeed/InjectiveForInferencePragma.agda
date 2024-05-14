-- Andre Knispel, Ulf, PR #6640, patched 2024-03-05 by Andreas

{-# OPTIONS --no-require-unique-meta-solutions #-}

module InjectiveForInferencePragma where

open import Agda.Builtin.Equality

module Concrete {A : Set} where

  open import Agda.Builtin.List

  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  reverse : List A → List A
  reverse []      = []
  reverse (x ∷ l) = reverse l ++ (x ∷ [])

  {-# INJECTIVE_FOR_INFERENCE reverse #-}

  postulate
    reverse-≡ : {l l' : List A} → reverse l ≡ reverse l' → reverse l ≡ reverse l'
    -- or define as: reverse-≡ h = h

  []≡[] : [] ≡ []
  []≡[] = reverse-≡ (refl {x = reverse []})

  -- Without lossy unification for `reverse`, Agda won't solve `l` and `l'` for `[]`,
  -- even though it knows `reverse l = reverse []`.

module Abstract {A : Set} where

  data List : Set where
    [] : List
    _∷_ : A → List → List

  _++_ : List → List → List
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  abstract
    reverse : List → List
    reverse []      = []
    reverse (x ∷ l) = reverse l ++ (x ∷ [])

  -- The pragma also works on abstract definitions.
  {-# INJECTIVE_FOR_INFERENCE reverse #-}

  postulate
    reverse-≡ : {l l' : List} → reverse l ≡ reverse l' → reverse l ≡ reverse l'

  abstract
    []≡[] : [] ≡ []
    []≡[] = reverse-≡ (refl {x = reverse []})
