postulate
  ⊥ : Set
  X : Set
  C : Set → Set

  instance
    CA : ∀ {A : Set} ⦃ _ : ⊥ ⦄ → C A -- this instance must come first to trigger the bug
    CX : C X
  {-# INCOHERENT CA #-}

  x! : .⦃ C X ⦄ → X

x : X
x = x!
