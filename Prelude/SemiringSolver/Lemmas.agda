------------------------------------------------------------------------
-- Some boring lemmas used by the semiring solver
------------------------------------------------------------------------

-- Note that these proofs use all commutative semiring properties
-- except for the fact that 0# is a zero for _*_.

open import Prelude.Algebraoid

module Prelude.SemiringSolver.Lemmas (s : CommutativeSemiringoid) where

open import Prelude.BinaryRelation
open import Prelude.Function
open import Prelude.Product
open Π
import Prelude.PreorderProof
import Prelude.Algebra
private
  open module R = CommutativeSemiringoid s
  open module S = Setoid setoid
  open module S = Equivalence equiv
  open module S = Prelude.PreorderProof (setoid⟶preSetoid setoid)
  open module R = Prelude.Algebra setoid
  module R = CommutativeSemiring commSemiring
  module R = Semiring R.semiring
  module A = CommutativeMonoid R.+-monoid
  module A = Monoid A.monoid
  module A = Semigroup A.semigroup
  module M = Monoid R.*-monoid
  module M = Semigroup M.semigroup

abstract
  lemma₁ :  forall a b c d x
         -> ((a + b) * x + (c + d)) ≈ (((a * x) + c) + ((b * x) + d))
  lemma₁ a b c d x =
    (a + b) * x + (c + d)
                                   ≃⟨ proj₂ R.distrib _ _ _ ⟨ A.•-pres-≈ ⟩ byDef ⟩
    ((a * x) + (b * x)) + (c + d)
                                   ≃⟨ sym $ A.assoc _ _ _ ⟩
    (a * x) + ((b * x) + (c + d))
                                   ≃⟨ byDef ⟨ A.•-pres-≈ ⟩ A.assoc _ _ _ ⟩
    (a * x) + (((b * x) + c) + d)
                                   ≃⟨ byDef ⟨ A.•-pres-≈ ⟩ (A.comm _ _ ⟨ A.•-pres-≈ ⟩ byDef) ⟩
    (a * x) + ((c + (b * x)) + d)
                                   ≃⟨ byDef ⟨ A.•-pres-≈ ⟩ sym (A.assoc _ _ _) ⟩
    (a * x) + (c + ((b * x) + d))
                                   ≃⟨ A.assoc _ _ _ ⟩
    ((a * x) + c) + ((b * x) + d)
                                   ∎

  lemma₂ : forall x y z -> (x + (y + z)) ≈ (y + (x + z))
  lemma₂ x y z =
    x + (y + z)
                 ≃⟨ A.assoc _ _ _ ⟩
    (x + y) + z
                 ≃⟨ A.comm _ _ ⟨ A.•-pres-≈ ⟩ byDef ⟩
    (y + x) + z
                 ≃⟨ sym $ A.assoc _ _ _ ⟩
    y + (x + z)
                 ∎

  lemma₃ :  forall a b c x
         -> (((a * c) * x) + (b * c))  ≈ (((a * x) + b) * c)
  lemma₃ a b c x =
    ((a * c) * x) + (b * c)
                             ≃⟨ lem ⟨ A.•-pres-≈ ⟩ byDef ⟩
    ((a * x) * c) + (b * c)
                             ≃⟨ sym $ proj₂ R.distrib _ _ _ ⟩
    ((a * x) + b) * c
                             ∎
    where
    lem =
      (a * c) * x
                   ≃⟨ sym (M.assoc _ _ _) ⟩
      a * (c * x)
                   ≃⟨ byDef ⟨ M.•-pres-≈ ⟩ R.*-comm _ _ ⟩
      a * (x * c)
                   ≃⟨ M.assoc _ _ _ ⟩
      (a * x) * c
                   ∎

  lemma₄ :  forall a b c x
         -> (((a * b) * x) + (a * c)) ≈ (a * ((b * x) + c))
  lemma₄ a b c x =
    ((a * b) * x) + (a * c)
                             ≃⟨ sym (M.assoc _ _ _)
                                  ⟨ A.•-pres-≈ ⟩
                                byDef ⟩
    (a * (b * x)) + (a * c)
                             ≃⟨ sym $ proj₁ R.distrib _ _ _ ⟩
    a * ((b * x) + c)
                             ∎

  lemma₅ : forall a b c d x
         -> ((((a * c) * x) * x) +
             ((((a * d) + (b * c)) * x) + (b * d))) ≈
            (((a * x) + b) * ((c * x) + d))
  lemma₅ a b c d x =
    (((a * c) * x) * x) +
    ((((a * d) + (b * c)) * x) + (b * d))
                                             ≃⟨ lem₁ ⟨ A.•-pres-≈ ⟩
                                                (lem₂ ⟨ A.•-pres-≈ ⟩ byDef) ⟩
    ((a * x) * (c * x)) +
    ((((a * x) * d) + (b * (c * x))) +
     (b * d))
                                             ≃⟨ byDef ⟨ A.•-pres-≈ ⟩ sym (A.assoc _ _ _) ⟩
    ((a * x) * (c * x)) +
    (((a * x) * d) +
     ((b * (c * x)) + (b * d)))
                                             ≃⟨ A.assoc _ _ _ ⟩
    (((a * x) * (c * x)) + ((a * x) * d)) +
    ((b * (c * x)) + (b * d))
                                             ≃⟨ sym $ proj₁ R.distrib _ _ _
                                                      ⟨ A.•-pres-≈ ⟩
                                                    proj₁ R.distrib _ _ _ ⟩
    ((a * x) * ((c * x) + d)) +
    (b * ((c * x) + d))
                                             ≃⟨ sym $ proj₂ R.distrib _ _ _ ⟩
    ((a * x) + b) * ((c * x) + d)
                                             ∎
    where
    lem₁' =
      (a * c) * x
                   ≃⟨ sym $ M.assoc _ _ _ ⟩
      a * (c * x)
                   ≃⟨ byDef ⟨ M.•-pres-≈ ⟩ R.*-comm _ _ ⟩
      a * (x * c)
                   ≃⟨ M.assoc _ _ _ ⟩
      (a * x) * c
                   ∎

    lem₁ =
      ((a * c) * x) * x
                         ≃⟨ lem₁' ⟨ M.•-pres-≈ ⟩ byDef ⟩
      ((a * x) * c) * x
                         ≃⟨ sym $ M.assoc _ _ _ ⟩
      (a * x) * (c * x)
                         ∎

    lem₂ =
      ((a * d) + (b * c)) * x
                                     ≃⟨ proj₂ R.distrib _ _ _ ⟩
      ((a * d) * x) + ((b * c) * x)
                                     ≃⟨ sym $ M.assoc _ _ _ ⟨ A.•-pres-≈ ⟩ M.assoc _ _ _ ⟩
      (a * (d * x)) + (b * (c * x))
                                     ≃⟨ (byDef ⟨ M.•-pres-≈ ⟩ R.*-comm _ _)
                                          ⟨ A.•-pres-≈ ⟩ byDef ⟩
      (a * (x * d)) + (b * (c * x))
                                     ≃⟨ M.assoc _ _ _ ⟨ A.•-pres-≈ ⟩ byDef ⟩
      ((a * x) * d) + (b * (c * x))
                                     ∎

  lemma₆ : forall x -> ((1# * x) + 0#) ≈ x
  lemma₆ x =
    (1# * x) + 0#
                   ≃⟨ proj₂ A.identity _ ⟩
    1# * x
                   ≃⟨ proj₁ M.identity _ ⟩
    x
                   ∎
