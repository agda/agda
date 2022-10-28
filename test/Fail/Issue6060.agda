{-# OPTIONS --cubical --prop -WnoUnsupportedIndexedMatch #-}

open import Agda.Builtin.Equality

data S : Set where s : S
data P : Prop where p : P

-- OK
f : (x : S) → P → s ≡ x → S
f .s y refl = s

-- Panic
g : (x : S) → s ≡ x → P → S
g .s refl y = s
