-- Andreas, 2015-03-17
-- Andreas, 2020-10-26 conform to Issue1428a

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

data ⊥ : Set where

data SizeLt (i : Size) : Set where
  wrap : Size< i → SizeLt i

-- This definition of size predecessor should be forbidden...
module _ (i : Size) where
  postulate
    pred : Size< i

-- ...otherwise the injectivity test loops here.
iter : ∀ i → SizeLt i → ⊥
iter i (wrap j) = iter j (wrap (pred j))

loop : Size → ⊥
loop i = iter i (wrap (pred i))

absurd : ⊥
absurd = FIXME loop ∞

-- Testcase temporarily mutilated, original error:
--
-- -Issue1428c.agda:...
-- -We don't like postulated sizes in parametrized modules.
--
-- +Issue1428c.agda:...
-- +Not in scope:
-- +  FIXME at Issue1428c.agda:...
-- +when scope checking FIXME
