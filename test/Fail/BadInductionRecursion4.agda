{-# NON_TERMINATING #-}

mutual

  record R : Set where
    inductive; no-eta-equality
    field
      x : T

  T : Set
  T = T → R
