{-# OPTIONS --erasure #-}

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

primitive
  primEraseEquality : ∀ {@0 a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
