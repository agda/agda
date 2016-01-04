
{-# TERMINATING         #-}
{-# NO_POSITIVITY_CHECK #-}
mutual
  data D₁ : Set where
    lam : (D₁ → D₁) → D₁

  Foo₁ : Set
  Foo₁ = Foo₁

{-# NON_TERMINATING     #-}
{-# NO_POSITIVITY_CHECK #-}
mutual
  data D₂ : Set where
    lam : (D₂ → D₂) → D₂

  Foo₂ : Set
  Foo₂ = Foo₂
