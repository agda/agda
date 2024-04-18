{-# OPTIONS --no-require-unique-meta-solutions #-}
module InjectiveForInferencePragma where

open import Agda.Builtin.Equality
open import Agda.Builtin.List

module _ {A : Set} where
  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  reverse : List A → List A
  reverse []      = []
  reverse (x ∷ l) = reverse l ++ (x ∷ [])

  {-# INJECTIVE_FOR_INFERENCE reverse #-}

  reverse-≡ : {l l' : List A} → reverse l ≡ reverse l' → reverse l ≡ reverse l'
  reverse-≡ h = h

  []≡[] : {l l' : List A} → [] ≡ []
  []≡[] = reverse-≡ (refl {x = reverse []})
