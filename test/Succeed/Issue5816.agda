{-# OPTIONS --without-K --prop #-}

open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to Z; suc to S)

data _≤_ : ℕ → ℕ → Prop where
  z≤x : ∀ {x} → Z ≤ x
  s≤s : ∀ {x y} → x ≤ y → S x ≤ S y

x≤Sy : ∀ {x y} → x ≤ y → x ≤ S y
x≤Sy z≤x = z≤x
x≤Sy (s≤s p) = s≤s (x≤Sy p)
