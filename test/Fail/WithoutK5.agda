{-# OPTIONS --cubical-compatible --show-implicit #-}
-- {-# OPTIONS -v tc.data.sort:20 -v tc.lhs.split.well-formed:100 #-}

module WithoutK5 where

-- Equality defined with one index.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

weak-K : {A : Set} {a b : A} (p q : a ≡ b) (α β : p ≡ q) → α ≡ β
weak-K refl .refl refl refl = refl
