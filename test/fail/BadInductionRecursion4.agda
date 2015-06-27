{-# NON_TERMINATING #-}

mutual

  record R : Set where
    inductive
    field
      x : T

  T : Set
  T = T → R
