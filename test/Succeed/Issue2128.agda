{-# OPTIONS --erasure #-}

postulate
  A : Set
  I : (@erased _ : A) → Set
  R : A → Set
  f : ∀ (@erased x : A) (r : R x) → I x
 -- can now be used here ^
