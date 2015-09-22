-- Andreas, 2015-03-16

open import Common.Size
open import Common.Prelude

-- Note: the assumption of pred is absurd,
-- but still should not make Agda loop.

module _ (pred : ∀ i → Size< i) where

data D (i : Size) : Set where
  wrap : (j : Size< i) → D i

loop : ∀ i → D i → ⊥
loop i (wrap j) = loop j (wrap (pred j))
-- Loops during injectivity check

d : ∀ i → D i
d i = wrap (pred i)

absurd : ⊥
absurd = loop ∞ (d ∞)
