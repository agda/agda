{-# OPTIONS --sized-types #-}

-- Andreas, 2026-10-12, issue #8829
-- Moved from test/Succeed.
-- Only the first size index of a data type is recognized as a size
-- of a sized type (it is covariant), the second index j of Heap is invariant.
-- Thus, Heap i j is not lower semi-continuous in j and the successor
-- pattern .(↑ j) does not provide termination evidence.

open import Common.Size

data Heap : (i j : Size) → Set where
  node : (i j : Size) → Heap (↑ i) (↑ j)

postulate
  _∪_ : Heap ∞ ∞ → Heap ∞ ∞ → Heap ∞ ∞
  mkH : ∀ i j → Heap i j

merge : (i j : Size) → Heap i j → Heap ∞ ∞
merge .(↑ i) .(↑ j) (node i j) with Set
merge .(↑ i) .(↑ j) (node i j) | _ =
  merge i (↑ j) (mkH i (↑ j)) ∪
  merge (↑ i) j (mkH (↑ i) j)
