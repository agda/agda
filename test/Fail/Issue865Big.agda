{-# OPTIONS --cubical-compatible #-}
-- {-# OPTIONS -v tc.data:100 #-}
module Issue865Big where

data _≡_ (A : Set) : Set → Set₁ where
  refl : A ≡ A

K : {A : Set} (P : A ≡ A → Set) → P refl → (p : A ≡ A) → P p
K P h refl = h
