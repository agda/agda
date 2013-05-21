{-# OPTIONS --without-K #-}

module WithoutK12 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- The --without-K option works with pattern matching lambdas.
K : (A : Set)(x : A)(P : x ≡ x → Set) → P refl → (p : x ≡ x ) →  P p
K A x P pr = λ {refl → pr}
