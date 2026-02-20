{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

module LocalRewriteNotBound where

module _ (n : Nat) (@rew p : ∀ {m} → n ≡ m) where
