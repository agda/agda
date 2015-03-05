-- Andreas, 2014-09-23, later changed by someone else
-- Issue 1194, reported by marco.vax91, 2014-06-13

module _ where

module A where

  data D₁ : Set where
    b : D₁
    c : D₁ → D₁

  infix 19 c

  syntax c x = ! x

module B where

  data D₂ : Set where
    _+_ : D₂ → D₂ → D₂
    c   : A.D₁ → D₂

  infix 10 _+_
  infix 20 c

  syntax c x = ! x

open A
open B

test : D₂
test = (! b) + (! b)
