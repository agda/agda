------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.Algebra.RingProperties (r : Ringoid) where

open import Prelude.BinaryRelation
open import Prelude.Function
open import Prelude.Product
open Π
import Prelude.PreorderProof
import Prelude.Algebra
private
  open module R  = Ringoid r
  open module S  = Setoid setoid
  open module E  = Equivalence equiv
  open module PP = Prelude.PreorderProof (setoid⟶preSetoid setoid)
  open module R  = Prelude.Algebra setoid
  module R = Ring R.ring
  module A = AbelianGroup R.+-group
  module A = Group A.group
  module A = Monoid A.monoid
  module A = Semigroup A.semigroup
  module M = Monoid R.*-monoid
  module M = Semigroup M.semigroup

abstract
  zero : Zero 0# _*_
  zero = zeroˡ , zeroʳ
    where
    zeroˡ : LeftZero 0# _*_
    zeroˡ x =
      0# * x
                                          ≃⟨ sym $ proj₂ A.identity _ ⟩
      (0# * x) + 0#
                                          ≃⟨ byDef ⟨ A.•-pres-≈ ⟩ sym (proj₂ A.inverse _) ⟩
      (0# * x) + ((0# * x) + - (0# * x))
                                          ≃⟨ A.assoc _ _ _ ⟩
      ((0# * x) + (0# * x)) + - (0# * x)
                                          ≃⟨ sym (proj₂ R.distrib _ _ _) ⟨ A.•-pres-≈ ⟩ byDef ⟩
      ((0# + 0#) * x) + - (0# * x)
                                          ≃⟨ proj₂ A.identity _ ⟨ M.•-pres-≈ ⟩ byDef ⟨ A.•-pres-≈ ⟩ byDef ⟩
      (0# * x) + - (0# * x)
                                          ≃⟨ proj₂ A.inverse _ ⟩
      0#
                                          ∎

    zeroʳ : RightZero 0# _*_
    zeroʳ x =
      x * 0#
                                          ≃⟨ sym $ proj₂ A.identity _ ⟩
      (x * 0#) + 0#
                                          ≃⟨ byDef ⟨ A.•-pres-≈ ⟩ sym (proj₂ A.inverse _) ⟩
      (x * 0#) + ((x * 0#) + - (x * 0#))
                                          ≃⟨ A.assoc _ _ _ ⟩
      ((x * 0#) + (x * 0#)) + - (x * 0#)
                                          ≃⟨ sym (proj₁ R.distrib _ _ _) ⟨ A.•-pres-≈ ⟩ byDef ⟩
      (x * (0# + 0#)) + - (x * 0#)
                                          ≃⟨ byDef ⟨ M.•-pres-≈ ⟩ proj₂ A.identity _ ⟨ A.•-pres-≈ ⟩ byDef ⟩
      (x * 0#) + - (x * 0#)
                                          ≃⟨ proj₂ A.inverse _ ⟩
      0#
                                          ∎

  semiring : Semiring _+_ _*_ 0# 1#
  semiring = record
    { +-monoid = record
        { monoid = A.monoid
        ; comm   = A.comm
        }
    ; *-monoid = R.*-monoid
    ; distrib  = R.distrib
    ; zero     = zero
    }

abstract

  minusDistribˡ : forall x y -> ((- x) * y) ≈ (- (x * y))
  minusDistribˡ x y =
    (- x) * y
                                         ≃⟨ sym $ proj₂ A.identity _ ⟩
    ((- x) * y) + 0#
                                         ≃⟨ byDef ⟨ A.•-pres-≈ ⟩ sym (proj₂ A.inverse _) ⟩
    ((- x) * y) + ((x * y) + - (x * y))
                                         ≃⟨ A.assoc _ _ _  ⟩
    (((- x) * y) + (x * y)) + - (x * y)
                                         ≃⟨ sym (proj₂ R.distrib _ _ _) ⟨ A.•-pres-≈ ⟩ byDef ⟩
    (((- x) + x) * y) + - (x * y)
                                         ≃⟨ proj₁ A.inverse _ ⟨ M.•-pres-≈ ⟩ byDef ⟨ A.•-pres-≈ ⟩ byDef ⟩
    (0# * y) + - (x * y)
                                         ≃⟨ proj₁ zero _ ⟨ A.•-pres-≈ ⟩ byDef ⟩
    0# + - (x * y)
                                         ≃⟨ proj₁ A.identity _ ⟩
    - (x * y)
                                         ∎

  minusDistribʳ : forall x y -> (x * (- y)) ≈ (- (x * y))
  minusDistribʳ x y =
    x * (- y)
                                         ≃⟨ sym $ proj₁ A.identity _ ⟩
    0# + (x * (- y))
                                         ≃⟨ sym (proj₁ A.inverse _) ⟨ A.•-pres-≈ ⟩ byDef ⟩
    (- (x * y) + (x * y)) + (x * (- y))
                                         ≃⟨ sym $ A.assoc _ _ _  ⟩
    - (x * y) + ((x * y) + (x * (- y)))
                                         ≃⟨ byDef ⟨ A.•-pres-≈ ⟩ sym (proj₁ R.distrib _ _ _)  ⟩
    - (x * y) + (x * (y + - y))
                                         ≃⟨ byDef ⟨ A.•-pres-≈ ⟩ (byDef ⟨ M.•-pres-≈ ⟩ proj₂ A.inverse _) ⟩
    - (x * y) + (x * 0#)
                                         ≃⟨ byDef ⟨ A.•-pres-≈ ⟩ proj₂ zero _ ⟩
    - (x * y) + 0#
                                         ≃⟨ proj₂ A.identity _ ⟩
    - (x * y)
                                         ∎
