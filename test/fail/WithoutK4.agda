{-# OPTIONS --without-K #-}

module WithoutK4 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

foo : (f : {A : Set} → A → A) {A : Set} (x y : A) →
      x ≡ f y → f y ≡ x
foo f .(f y) y refl = refl
