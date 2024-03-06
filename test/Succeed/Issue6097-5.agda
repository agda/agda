-- Issue #6097, test case by Nils Anders.
--
-- 2024-03-06: modified by Andreas and Ulf.
-- Checking a long application is slow in Agda >= 2.5.4 && < 2.6.5
-- because the analysis whether to check the target first
-- is repeated at every step.

open import Agda.Builtin.Unit

module _ where

  postulate
    F : {A : Set₁} →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
      Set₁ → A

  _ : Set
  _ = F
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set Set Set Set Set Set Set Set Set Set
    Set
