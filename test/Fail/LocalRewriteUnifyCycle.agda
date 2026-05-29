{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module _ (f : Nat → Nat → Nat) (n m : Nat) (@rewrite p : n ≡ 0) where
  foo : f n m ≡ m → Nat
  foo refl = 0

