-- Andreas, 2014-05-20 Triggered by Andrea Vezzosi & NAD
{-# OPTIONS --copatterns --sized-types #-}
-- {-# OPTIONS -v tc.conv.coerce:10 #-}

open import Common.Size

-- Andreas, 2015-03-16: currently forbidden
-- Size≤ : Size → SizeUniv
-- Size≤ i = Size< ↑ i

postulate
  Dom    : Size → Set
  mapDom : ∀ i (j : Size< (↑ i)) → Dom i → Dom j

record ∞Dom i : Set where
  field
    force : ∀ (j : Size< i) → Dom j

∞mapDom : ∀ i (j : Size< (↑ i)) → ∞Dom i → ∞Dom j
∞Dom.force (∞mapDom i j x) k = mapDom k k (∞Dom.force x k)

-- The second k on the rhs has type
--   k : Size< j
-- and should have type
--   k : Size≤ k = Size< ↑ k
-- Since j <= ↑ k does not hold (we have only k < j),
-- we cannot do the usual subtyping  Size< j <= Size≤ k,
-- but we have to use the "singleton type property"
--   k : Size< ↑ k
