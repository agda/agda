{-# OPTIONS --sized-types #-}

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
