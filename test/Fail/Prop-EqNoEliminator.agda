{-# OPTIONS --prop #-}

data _≡P_ {A : Set} (x : A) : A → Prop where
  refl : x ≡P x

J-P : {A : Set} (x : A) (P : (y : A) → x ≡P y → Set)
    → P x refl → (y : A) (e : x ≡P y) → P y e
J-P x P p .x refl = p
