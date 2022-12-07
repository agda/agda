{-# OPTIONS --erasure #-}

open import Agda.Builtin.Unit

data D : Set where
  c₁ c₂ : D
  @0 c₃ : D

f : @0 D → ⊤
f c₁ = tt
f c₂ = tt
f c₃ = tt
