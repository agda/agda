
{-# NO_POSITIVITY_CHECK #-}
{-# TERMINATING         #-}
mutual
  data D₁ : Set where
    lam : (D₁ → D₁) → D₁

  Foo₁ : Set
  Foo₁ = Foo₁

{-# NO_POSITIVITY_CHECK #-}
{-# NON_TERMINATING     #-}
mutual
  data D₂ : Set where
    lam : (D₂ → D₂) → D₂

  Foo₂ : Set
  Foo₂ = Foo₂

{-# NO_POSITIVITY_CHECK  #-}
{-# NO_TERMINATION_CHECK #-}
mutual
  data D₃ : Set where
    lam : (D₃ → D₃) → D₃

  Foo₃ : Set
  Foo₃ = Foo₃
