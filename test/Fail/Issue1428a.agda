-- Andreas, 2015-03-16
-- Andreas, 2020-10-26 removed loop during injectivity check

open import Agda.Builtin.Size

-- Note: the assumption of pred is absurd,
-- but still should not make Agda loop.

module _ (pred : ∀ i → Size< i) where

data ⊥ : Set where

data SizeLt (i : Size) : Set where
  wrap : (j : Size< i) → SizeLt i

loop : (d : ∀ i → SizeLt i) → ∀ i → SizeLt i → ⊥
loop d i (wrap j) = loop d j (d j)

-- -- Loops during injectivity check:
-- loop : ∀ i → SizeLt i → ⊥
-- loop i (wrap j) = loop j (wrap (pred j))

d : ∀ i → SizeLt i
d i = wrap (pred i)

absurd : ⊥
absurd = loop d ∞ (d ∞)

_ = FIXME

-- Testcase temporarily mutilated, original error:
--
-- -Issue1428a.agda:..
-- -Functions may not return sizes, thus, function type
-- -(i : Size) → Size< i is illegal
-- -when checking that the expression ∀ i → Size< i is a type
--
-- +Issue1428a.agda:...
-- +Not in scope:
-- +  FIXME at Issue1428a.agda:...
-- +when scope checking FIXME
