{-# OPTIONS --cubical-compatible #-}

module WithoutK-PatternMatchingLambdas2 where

-- Equality defined with two indices.
data _≡_ {A : Set} : A → A → Set where
  refl : ∀ x → x ≡ x

-- The --cubical-compatible option works with pattern matching lambdas.
K : (A : Set) (x : A) (P : x ≡ x → Set) → P (refl x) → (p : x ≡ x ) →  P p
K = λ { A .x P pr (refl x) → pr }
