-- Andreas, 2016-10-11, AIM XXIV, issue #2250

{-# OPTIONS --injective-type-constructors #-}

open import Common.Prelude
open import Common.Equality

abstract
  f : Bool → Bool
  f x = true

  same : f true ≡ f false
  same = refl

-- f should not be treated as injective here,
-- even though f true and f false do not reduce.

not-same : f true ≡ f false → ⊥
not-same () -- should be yellow

absurd : ⊥
absurd = not-same same
