{-# OPTIONS --double-check --warning=noNotAffectedByOpaque #-}

module OpaqueRecordBoundaries where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- The fields belong to these records, rather than the enclosing opaque block.
opaque
  token : Nat
  token = zero

  record R : Set where
    constructor pack
    field value : Nat

  module M where
    record S : Set where
      constructor wrap
      field value : Nat

r : R
r = pack 3

_ : R.value r ≡ 3
_ = refl

s : M.S
s = M.wrap 4

_ : M.S.value s ≡ 4
_ = refl

-- Opaque helper blocks before and between fields remain legal.
record Staged : Set where
  opaque
    first : Nat
    first = zero
  field x : Nat
  opaque
    second : Nat
    second = x
  field y : Nat
