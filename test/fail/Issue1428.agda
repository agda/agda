-- Andreas, 2013-05-16, raised by Andrea 2015-02-10

open import Common.Size
open import Common.Prelude

data Wrap (A : SizeUniv) : SizeUniv where
-- data Wrap (A : Set) : Set where
  wrap : A → Wrap A

module M (f : ∀ i → Wrap (Size< i)) where

  test : ∀ i → Wrap (Size< i) → ⊥
  test i (wrap j) = test j (f j)

module N (pred : ∀ i → Size< i) where

  f = (λ i → wrap (pred i))
  open M f

  loop : Size → ⊥
  loop i = test i (f i)
  -- = test i (wrap (pred i))
  -- = test (pred i) ((λ i → wrap (pred i)) (pred i))
  -- = test (pred i) (wrap (pred (pred i)))
  -- = test (pred (pred i)) (wrap (pred (pred (pred i))))
  -- = ...
