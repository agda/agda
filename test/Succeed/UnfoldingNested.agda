module UnfoldingNested where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

module A where
  abstract
    foo : Nat
    foo = 2

module B where
  abstract
    bar : Nat
    bar = 2

module C where
  open A
  open B
  abstract unfolding (bar) where
    abstract unfolding (foo) where
      _ : foo + bar ≡ 4
      _ = refl
