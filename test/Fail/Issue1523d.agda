{-# OPTIONS --sized-types #-}

open import Common.Size

postulate
  A : Set
  f : Size → A

-- k' < k < j <= i + 2 =/=> ∃ l < i
test : ∀ i (j : Size< (↑ ↑ ↑ i)) (k : Size< j) (k' : Size< k) → Size → Set → (((l : Size< i) → A) → A) → A
test i j k k' _ _ ret = ret λ l → f l
