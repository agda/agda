{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  foo : Nat → Nat

module _ (@rewrite eq : (f : Nat → Nat) → f 0 ≡ 1) where
  weird : foo 0 ≡ 1
  weird = refl
