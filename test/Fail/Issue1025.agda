{-# OPTIONS --cubical-compatible #-}

module Issue1025 where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

postulate mySpace : Set
postulate myPoint : mySpace

data Foo : myPoint ≡ myPoint → Set where
  foo : Foo refl

test : {e : myPoint ≡ myPoint} → (a : Foo e) → (i : a ≡ a) → i ≡ refl
test foo refl = {!!}
