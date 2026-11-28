{-# OPTIONS --no-eta-singleton #-}

module NoEtaSingletonExplicit where

record ⊤ : Set where
  eta-equality
  constructor tt

data _≡_ (x : ⊤) : ⊤ → Set where
  refl : x ≡ x

test : (x y : ⊤) → x ≡ y
test x y = refl
