{-# OPTIONS --sized-types #-}

open import Common.Size

postulate
  A : Set
  f : Size → A

-- k < j ==> ∃ l < j
works : ∀ i (j : Size< (↑ i)) (k : Size< j) → (((l : Size< j) → A) → A) → A
works i j k ret = ret λ l → f l

-- k < j <= i ==> ∃ l < i
test1 : ∀ i (j : Size< (↑ i)) (k : Size< j) → (((l : Size< i) → A) → A) → A
test1 i j k ret = ret λ l → f l

-- k' < k < j <= i + 1 ==> ∃ l < i
test : ∀ i (j : Size< (↑ ↑ i)) (k : Size< j) (k' : Size< k) → (((l : Size< i) → A) → A) → A
test i j k k' ret = ret λ l → f l
