{-# OPTIONS --prop #-}

data _≡_ {X : Set} (a : X) : X → Prop where
  refl : a ≡ a

postulate
  A : Set
  P : Prop
  p : P
  u : P → A

f : {x : A} (q : u p ≡ x) → P
f refl = p   -- works in 2.6.0.1
