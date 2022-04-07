{-# OPTIONS --cubical-compatible --safe #-}

data E (@0 A : Set) : Set where
  c₁ c₂ : A → E A
  @0 c₃ : A → E A
