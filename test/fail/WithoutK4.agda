{-# OPTIONS --without-K #-}

module WithoutK4 where

data ⊥ : Set where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Bool : Set where
  true false : Bool

true≢false : true ≡ false → ⊥
true≢false ()
