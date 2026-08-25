{-# OPTIONS --cubical --safe #-}

-- Andreas, 2026-08-25, issue #8683, variant without `with`.
-- The principal argument of an ambiguous projection is elaborated in
-- inference mode, which used to skip the side conditions of the
-- cubical primitives.

open import Agda.Primitive.Cubical renaming (primHComp to hcomp)
open import Agda.Builtin.Nat

record R : Set where
  constructor mk
  field fst : Nat
open R

record S : Set where
  constructor mk'
  field fst : Nat
open S

-- The hcomp's base (mk 1) disagrees with its side (constantly (mk 0))
-- on φ = j, so this must be rejected.
bad : I → Nat
bad j = fst (hcomp {A = R} {φ = j} (λ i _ → mk 0) (mk 1))
