{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

module LocalRewriteNotEnabled where

module _ (n : Nat) (@rew p : n ≡ 0) where
