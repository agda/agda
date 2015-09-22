{-# NON_TERMINATING #-}

mutual

  data D : Set where
    c : T₁ → D

  T₁ : Set
  T₁ = T₂

  T₂ : Set
  T₂ = T₁ → D
