{-# OPTIONS --prop --cubical-compatible #-}

data _≡_ {A : Set} (x : A) : A → Prop where
  refl : x ≡ x
