{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  A : Set
  a b : A
  f : (A → A) → A
  g : A → A

  rewf₁ : f (λ x → g x) ≡ a
  rewf₂ : f (λ x → a) ≡ b

  rewg : (x : A) → g x ≡ a

{-# REWRITE rewf₁ rewf₂ rewg #-}
