{-# OPTIONS --cubical-compatible #-}

module WithoutK2 where

-- Equality defined with two indices.

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ x → x ≡ x

K : {A : Set} (P : {x : A} → x ≡ x → Set) →
    (∀ x → P (refl x)) →
    ∀ {x} (x≡x : x ≡ x) → P x≡x
K P p (refl x) = p x
