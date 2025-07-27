{-# OPTIONS --exact-split -Werror #-}
module InlineNoExactSplit where

open import Agda.Builtin.Sigma

record ⊤ : Set₁ where
  no-eta-equality
  field
    x : Set

{-# INLINE ⊤.constructor #-}

test : Σ Set₁ λ _ → ⊤
test .fst = Set
-- Warning should point to line 17 (the inlined clause) and not 14 (the
-- overall function).
test .snd = record {}
