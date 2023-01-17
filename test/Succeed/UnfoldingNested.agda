module UnfoldingNested where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

module A where
  opaque
    foo : Nat
    foo = 2

module B where
  opaque
    bar : Nat
    bar = 2

module C where
  open A
  open B
  -- No warning should be printed:
  opaque unfolding (bar) where
    opaque unfolding (foo) where
      _ : foo + bar ≡ 4
      _ = refl
