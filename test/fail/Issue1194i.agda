module _ where

module A where

  infix 0 c

  syntax c x = + x

  data D₁ : Set where
    b : D₁
    c : D₁ → D₁

module B where

  infix 1 c

  syntax c x = + x

  data D₂ : Set where
    c : A.D₁ → D₂

open A
open B

test₁ : D₂
test₁ = + + + b

test₂ : D₂ → D₁
test₂ (+ + x) = x
test₂ (+ b)   = + + + b
