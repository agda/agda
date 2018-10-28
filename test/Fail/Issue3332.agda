{-# OPTIONS --prop #-}

data _≡_ {A : Set} (a : A) : A → Prop where
  refl : a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}
