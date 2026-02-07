{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteBadMatch2 where

module _ (f : Nat → Nat) (x : Nat) (@rew p : f 1 ≡ 0) where
  foo : f ≡ (λ x → x) → Nat
  foo refl = 0
