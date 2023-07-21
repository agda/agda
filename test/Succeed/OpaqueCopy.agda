module OpaqueCopy where

open import Agda.Builtin.Nat
  using (Nat; zero; suc)
open import Agda.Builtin.Equality

module Opaque where

module M2 (A : Set) where
  opaque
    _+_ : Nat → Nat → Nat
    zero  + m = m
    suc n + m = suc (n + m)

module M3 (A : Set) where
  open M2 Nat public

module M4 where
  open M3 Nat public

module M5 where
  open M4

  opaque
    unfolding _+_

    _ : 1 + 1 ≡ 2
    _ = refl
