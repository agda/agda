-- {-# OPTIONS -v 100 -v tc.meta.name:100 -v interactive.meta:10 #-}
module Issue526 where

-- Don't just write _49,
-- include the corresponding implicit variable name as well (if any)

postulate
  f : {A : Set} → {a : A} → Set1 → {B : Set} → Set

test : Set
test = f Set

test₁ : Set
test₁ = f {A = _} Set

postulate
  g : (B : Set) → Set

test₂ : Set
test₂ = g _

test₃ : _ → Set
test₃ ()

