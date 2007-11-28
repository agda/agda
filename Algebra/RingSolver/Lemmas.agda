------------------------------------------------------------------------
-- Some boring lemmas used by the ring solver
------------------------------------------------------------------------

-- Note that these proofs use all "almost commutative ring" properties
-- except for the fact that 0# is a zero for *.

open import Algebra.Packaged

module Algebra.RingSolver.Lemmas
  (coeff : BareRingoid)
  (r : AlmostCommRingoid)
  (morphism : coeff -Bare-AlmostComm⟶ r)
  where

open import Relation.Binary
open import Data.Function
open import Data.Product
import Relation.Binary.EqReasoning
import Algebra
import Algebra.Morphism as Morphism
private
  open module R = AlmostCommRingoid r
  open module R = BareRingoid bare
  open module S = SetoidOps setoid
  open module S = Relation.Binary.EqReasoning preorder
  open module R = Algebra setoid
  open module R = AlmostCommRing almostCommRing
  open module R = CommutativeSemiring commSemiring
  open module R = Semiring semiring
  module A = CommutativeMonoid +-monoid
  module A = Monoid A.monoid
  module A = Semigroup A.semigroup
  module M = Monoid *-monoid
  module M = Semigroup M.semigroup
  module C = BareRingoid coeff
  module C = Setoid C.setoid
  open module R = Morphism C.setoid setoid
  open module R = RingHomomorphism morphism

abstract

  lemma₀ : forall x -> (x + ⟦ C.0# ⟧) ≈ x
  lemma₀ x =
                  begin
    x + ⟦ C.0# ⟧
                  ∼⟨ byDef ⟨ A.•-pres-≈ ⟩ 0-homo ⟩
    x + 0#
                  ∼⟨ proj₂ A.identity _ ⟩
    x
                  ∎

  lemma₁ :  forall a b c d x
         -> (((a + b) * x) + (c + d)) ≈ (((a * x) + c) + ((b * x) + d))
  lemma₁ a b c d x =
                                   begin
    ((a + b) * x) + (c + d)
                                   ∼⟨ proj₂ distrib _ _ _ ⟨ A.•-pres-≈ ⟩ byDef ⟩
    ((a * x) + (b * x)) + (c + d)
                                   ∼⟨ sym $ A.assoc _ _ _ ⟩
    (a * x) + ((b * x) + (c + d))
                                   ∼⟨ byDef ⟨ A.•-pres-≈ ⟩ A.assoc _ _ _ ⟩
    (a * x) + (((b * x) + c) + d)
                                   ∼⟨ byDef ⟨ A.•-pres-≈ ⟩ (A.comm _ _ ⟨ A.•-pres-≈ ⟩ byDef) ⟩
    (a * x) + ((c + (b * x)) + d)
                                   ∼⟨ byDef ⟨ A.•-pres-≈ ⟩ sym (A.assoc _ _ _) ⟩
    (a * x) + (c + ((b * x) + d))
                                   ∼⟨ A.assoc _ _ _ ⟩
    ((a * x) + c) + ((b * x) + d)
                                   ∎

  lemma₂ : forall x y z -> (x + (y + z)) ≈ (y + (x + z))
  lemma₂ x y z =
                 begin
    x + (y + z)
                 ∼⟨ A.assoc _ _ _ ⟩
    (x + y) + z
                 ∼⟨ A.comm _ _ ⟨ A.•-pres-≈ ⟩ byDef ⟩
    (y + x) + z
                 ∼⟨ sym $ A.assoc _ _ _ ⟩
    y + (x + z)
                 ∎

  lemma₃ :  forall a b c x
         -> (((a * c) * x) + (b * c))  ≈ (((a * x) + b) * c)
  lemma₃ a b c x =
                             begin
    ((a * c) * x) + (b * c)
                             ∼⟨ lem ⟨ A.•-pres-≈ ⟩ byDef ⟩
    ((a * x) * c) + (b * c)
                             ∼⟨ sym $ proj₂ distrib _ _ _ ⟩
    ((a * x) + b) * c
                             ∎
    where
    lem =
                   begin
      (a * c) * x
                   ∼⟨ sym (M.assoc _ _ _) ⟩
      a * (c * x)
                   ∼⟨ byDef ⟨ M.•-pres-≈ ⟩ *-comm _ _ ⟩
      a * (x * c)
                   ∼⟨ M.assoc _ _ _ ⟩
      (a * x) * c
                   ∎

  lemma₄ :  forall a b c x
         -> (((a * b) * x) + (a * c)) ≈ (a * ((b * x) + c))
  lemma₄ a b c x =
                             begin
    ((a * b) * x) + (a * c)
                             ∼⟨ sym (M.assoc _ _ _)
                                  ⟨ A.•-pres-≈ ⟩
                                byDef ⟩
    (a * (b * x)) + (a * c)
                             ∼⟨ sym $ proj₁ distrib _ _ _ ⟩
    a * ((b * x) + c)
                             ∎

  lemma₅ : forall a b c d x
         -> ((((a * c) * x) * x) +
             ((((a * d) + (b * c)) * x) + (b * d))) ≈
            (((a * x) + b) * ((c * x) + d))
  lemma₅ a b c d x =
                                             begin
    (((a * c) * x) * x) +
    ((((a * d) + (b * c)) * x) + (b * d))
                                             ∼⟨ lem₁ ⟨ A.•-pres-≈ ⟩
                                                (lem₂ ⟨ A.•-pres-≈ ⟩ byDef) ⟩
    ((a * x) * (c * x)) +
    ((((a * x) * d) + (b * (c * x))) +
     (b * d))
                                             ∼⟨ byDef ⟨ A.•-pres-≈ ⟩ sym (A.assoc _ _ _) ⟩
    ((a * x) * (c * x)) +
    (((a * x) * d) +
     ((b * (c * x)) + (b * d)))
                                             ∼⟨ A.assoc _ _ _ ⟩
    (((a * x) * (c * x)) + ((a * x) * d)) +
    ((b * (c * x)) + (b * d))
                                             ∼⟨ sym $ proj₁ distrib _ _ _
                                                      ⟨ A.•-pres-≈ ⟩
                                                    proj₁ distrib _ _ _ ⟩
    ((a * x) * ((c * x) + d)) +
    (b * ((c * x) + d))
                                             ∼⟨ sym $ proj₂ distrib _ _ _ ⟩
    ((a * x) + b) * ((c * x) + d)
                                             ∎
    where
    lem₁' =
                   begin
      (a * c) * x
                   ∼⟨ sym $ M.assoc _ _ _ ⟩
      a * (c * x)
                   ∼⟨ byDef ⟨ M.•-pres-≈ ⟩ *-comm _ _ ⟩
      a * (x * c)
                   ∼⟨ M.assoc _ _ _ ⟩
      (a * x) * c
                   ∎

    lem₁ =
                         begin
      ((a * c) * x) * x
                         ∼⟨ lem₁' ⟨ M.•-pres-≈ ⟩ byDef ⟩
      ((a * x) * c) * x
                         ∼⟨ sym $ M.assoc _ _ _ ⟩
      (a * x) * (c * x)
                         ∎

    lem₂ =
                                     begin
      ((a * d) + (b * c)) * x
                                     ∼⟨ proj₂ distrib _ _ _ ⟩
      ((a * d) * x) + ((b * c) * x)
                                     ∼⟨ sym $ M.assoc _ _ _ ⟨ A.•-pres-≈ ⟩ M.assoc _ _ _ ⟩
      (a * (d * x)) + (b * (c * x))
                                     ∼⟨ (byDef ⟨ M.•-pres-≈ ⟩ *-comm _ _)
                                          ⟨ A.•-pres-≈ ⟩ byDef ⟩
      (a * (x * d)) + (b * (c * x))
                                     ∼⟨ M.assoc _ _ _ ⟨ A.•-pres-≈ ⟩ byDef ⟩
      ((a * x) * d) + (b * (c * x))
                                     ∎

  lemma₆ : forall a b x -> (((- a) * x) + (- b)) ≈ (- ((a * x) + b))
  lemma₆ a b x =
                         begin
    ((- a) * x) + (- b)
                         ∼⟨ ¬-*-distribˡ _ _ ⟨ A.•-pres-≈ ⟩ byDef ⟩
    (- (a * x)) + (- b)
                         ∼⟨ ¬-+-comm _ _ ⟩
    - ((a * x) + b)
                         ∎

  lemma₇ : forall x -> ((⟦ C.1# ⟧ * x) + ⟦ C.0# ⟧) ≈ x
  lemma₇ x =
                                begin
    ((⟦ C.1# ⟧ * x) + ⟦ C.0# ⟧)
                                ∼⟨ (1-homo ⟨ M.•-pres-≈ ⟩ byDef) ⟨ A.•-pres-≈ ⟩ 0-homo ⟩
    (1# * x) + 0#
                                ∼⟨ proj₂ A.identity _ ⟩
    1# * x
                                ∼⟨ proj₁ M.identity _ ⟩
    x
                                ∎
