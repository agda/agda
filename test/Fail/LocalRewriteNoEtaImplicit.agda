{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

module LocalRewriteNoEtaImplicit where

module _ (n : Nat) {@rewrite p : n ≡ 0} where
  foo : Nat
  foo = 42

test : foo 0 ≡ foo 1
test = refl
