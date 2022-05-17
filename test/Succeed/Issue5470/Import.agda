{-# OPTIONS --rewriting #-}

module Issue5470.Import where

open import Agda.Builtin.Nat

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

private
  postulate
    foo : Nat → Nat

bar : Nat → Nat
bar n = foo n

private
  postulate
    lemma : ∀ n → foo n ≡ n
  {-# REWRITE lemma #-}
