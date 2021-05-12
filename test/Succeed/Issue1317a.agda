{-# OPTIONS --allow-unsolved-metas --sized-types #-}

open import Common.Size

-- An abuse of sized types, but as you wish...

data D (i : Size) : Set where
  c  : (j : Size< i) (k : Size< j) (l : Size< k) (m : Size< l) → D m → D i
  c' : (j : Size< i) → D j → D i

works : ∀ i → D i → Set
works i (c j k l m d) = works j (c' k (c' l (c' m d)))
works i (c' j d)      = works j d

test : ∀ i → D i → Set
test i (c j k l m d) = test ? (c' ? (c' ? (c' ? ?)))
test i (c' j d) = ?

-- Should not give a termination error as there is an instantiation
-- of meta variables that gives a terminating function.
