{-# OPTIONS --cubical-compatible #-}

module WithoutK-PatternMatchingLambdas1 where

-- Equality defined with one index.
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- The --cubical-compatible option works with pattern matching lambdas.
K : (A : Set) (x : A) (P : x ≡ x → Set) → P refl → (p : x ≡ x ) →  P p
K = λ { A x P pr refl → pr }
