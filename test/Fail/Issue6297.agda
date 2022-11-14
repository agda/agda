{-# OPTIONS --without-K #-}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

refl′ : (A : Set) (@0 x : A) → x ≡ x
refl′ A x = refl {A = A} {x = x}
