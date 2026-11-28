{-# OPTIONS --no-eta-singleton #-}

module NoEtaSingleton where

record ⊤ : Set where
  constructor tt

data _≡_ (x : ⊤) : ⊤ → Set where
  refl : x ≡ x

test : (x y : ⊤) → x ≡ y
test x y = refl
