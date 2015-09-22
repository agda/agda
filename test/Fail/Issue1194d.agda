-- Andreas, 2014-09-23, later changed by someone else
-- Issue 1194, reported by marco.vax91, 2014-06-13

module _ where

module A where

  data D₁ : Set where
    b : D₁
    c : D₁ → D₁

  infix 39 c

  syntax c x = ! x

module B where

  data D₂ : Set where
    _+_ : D₂ → D₂ → D₂
    c   : A.D₁ → D₂

  infix 30 _+_
  infix 40 c

  syntax c x = ! x

open A
open B

-- Should fail, because the fixity of A.c differs from that of B.c, so
-- they both get the default fixity (infix 20).

test : D₂
test = ! b + ! b
