{-# OPTIONS --without-K #-}

open import Agda.Builtin.Equality
open import Agda.Primitive using (Setω)

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  refl : x ≡ω x

congω : {A : Set} {B : Setω} (f : A → B)
      → ∀ {x y} → x ≡ y → f x ≡ω f y
congω f refl = refl
