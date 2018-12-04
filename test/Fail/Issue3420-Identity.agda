{-# OPTIONS --without-K #-}

open import Agda.Primitive

data _≡_ {a} {A : Set a} (x : A) : A → Set where
  refl : x ≡ x
