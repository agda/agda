{-# OPTIONS --no-eta-singleton #-}

module NoEtaSingletonRecord where

record ⊤ : Set where
  constructor tt

record R : Set where
  field f : ⊤

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

t : ⊤
t = tt

-- R still has eta-equality because it has a usable field.
etaR : (x : R) → x ≡ record { f = R.f x }
etaR x = refl
