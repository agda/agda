{-# OPTIONS --cubical-compatible #-}
postulate
  A : Set
  B : A → Set

@0 T : Set
T = (@0 x : A) → B x

_ : Set₁
_ = (@0 A : Set) → @0 A → (@0 x : A) → Set

data D : Set₁ where
  @0 c : (@0 A : Set) → A → (x : A) → D
