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
absurd = loop ∞
