{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  A : Set
  a b : A

  f : (X : Set) → X → A
  g : (X : Set) → X

  rewf₁ : f (A → A) (λ _ → a) ≡ a
  rewf₂ : (X : Set) → f X (g X) ≡ b

  rewg : (x : A) → g (A → A) x ≡ a

test = f (A → A) (λ x → g (A → A) x)

{-# REWRITE rewf₁ rewg #-}

foo : test ≡ a
foo = refl

{-# REWRITE rewf₂ #-}

bar : test ≡ b
bar = refl

fails : a ≡ b
fails = refl
