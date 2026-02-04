{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  f : Nat → Nat

module _ (x : Nat) (@rew _ : f x ≡ 0) where
  test : f x ≡ 0
  test = refl
