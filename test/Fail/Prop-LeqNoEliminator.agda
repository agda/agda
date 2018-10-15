{-# OPTIONS --prop #-}

-- Trying to define ≤ as a datatype in Prop doesn't work very well:

open import Agda.Builtin.Nat

data _≤'_ : Nat → Nat → Prop where
  zero : (y : Nat) → zero ≤' y
  suc  : (x y : Nat) → x ≤' y → suc x ≤' suc y

≤'-ind : (P : (m n : Nat) → Set)
       → (pzy : (y : Nat) → P zero y)
       → (pss : (x y : Nat) → P x y → P (suc x) (suc y))
       → (m n : Nat) → m ≤' n → P m n
≤'-ind P pzy pss .0 y (zero .y) = ?
≤'-ind P pzy pss .(suc x) .(suc y) (suc x y pf) = ?
