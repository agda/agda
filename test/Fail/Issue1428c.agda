-- Andreas, 2015-03-17

open import Common.Size

data ⊥ : Set where

data D (i : Size) : Set where
  c : Size< i → D i

-- This definition of size predecessor should be forbidden...
module _ (i : Size) where
  postulate
    pred : Size< i

-- ...otherwise the injectivity test loops here.
iter : ∀ i → D i → ⊥
iter i (c j) = iter j (c (pred j))

loop : Size → ⊥
loop i = iter i (c (pred i))

absurd : ⊥
absurd = FIXME loop ∞

-- Testcase temporarily mutilated, original error
-- -Issue1428c.agda:13,5-19
-- -We don't like postulated sizes in parametrized modules.
-- +Issue1428c.agda:23,10-15
-- +Not in scope:
-- +  FIXME at Issue1428c.agda:23,10-15
-- +when scope checking FIXME
