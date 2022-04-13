{-# OPTIONS --cubical-compatible #-}

module WithoutK1 where

-- Equality defined with one index.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

K : {A : Set} (P : {x : A} → x ≡ x → Set) →
    (∀ x → P (refl {x = x})) →
    ∀ {x} (x≡x : x ≡ x) → P x≡x
K P p refl = p _
