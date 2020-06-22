{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

record Box (A : Set) : Set where
  constructor box
  field
    unbox : A
open Box

postulate
  A : Set
  a b : A

  f : (X : Set) → X → A
  g : (X : Set) → X

  rewf₁ : f (Box A) (box a) ≡ a
  rewf₂ : (X : Set) → f X (g X) ≡ b

  rewg : g (Box A) .unbox ≡ a

test = f (Box A) (g (Box A))

{-# REWRITE rewf₁ rewg #-}

rewg-contracted : g (Box A) ≡ box a
rewg-contracted = refl

foo : test ≡ a
foo = refl

{-# REWRITE rewf₂ #-}

bar : test ≡ b
bar = refl

fails : a ≡ b
fails = refl
