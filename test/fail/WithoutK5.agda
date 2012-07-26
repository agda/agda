{-# OPTIONS --without-K --show-implicit #-}

module WithoutK5 where

-- Equality defined with one index.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

weak-K : {A : Set} {a b : A} (p q : a ≡ b) (α β : p ≡ q) → α ≡ β
weak-K refl .refl refl refl = refl
