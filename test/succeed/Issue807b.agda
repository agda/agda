module Issue807b where

open import Common.Coinduction

data Unit : Set where
  unit : Unit

From-unit : Unit → Set
From-unit unit = Unit

from-unit : (x : Unit) → From-unit x
from-unit unit = unit

data D : Set where
  d₁ : D
  d₂ : ∞ D → D

foo : D → Unit
foo d₁     = unit
foo (d₂ x) with ♭ x
foo (d₂ x) | d₁   = unit
foo (d₂ x) | d₂ _ = unit

-- x : ∞ D
x = ♯ d₁

-- There was an internal error if type-signature was not supplied.
