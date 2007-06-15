------------------------------------------------------------------------
-- Some derivable properties
------------------------------------------------------------------------

open import Prelude.Algebraoid

module Prelude.Algebra.BooleanAlgebraProperties
  (b : BooleanAlgebraoid)
  where

open import Prelude.BinaryRelation
open import Prelude.Function
open import Prelude.Product
open Π
import Prelude.PreorderProof
import Prelude.Algebra
import Prelude.Algebra.LatticeProperties
private
  open module B = BooleanAlgebraoid b
  open module B = Prelude.Algebra setoid
  open module B = BooleanAlgebra booleanAlgebra
  open module B = Lattice lattice
  open module S = Setoid setoid
  open module S = Equivalence equiv
  open module S = Preorder preorder
  open module S = Prelude.PreorderProof (setoid⟶preSetoid setoid)
  module LP = Prelude.Algebra.LatticeProperties (boolAlgoid⟶latticoid b)
open LP public

abstract
  ∨-∧-distribʳ : _∨_ DistributesOverʳ _∧_
  ∨-∧-distribʳ x y z =
    (y ∧ z) ∨ x
                       ≃⟨ ∨-comm _ _ ⟩
    x ∨ (y ∧ z)
                       ≃⟨ ∨-∧-distrib _ _ _ ⟩
    (x ∨ y) ∧ (x ∨ z)
                       ≃⟨ ∨-comm _ _ ⟨ ∧-pres-≈ ⟩ ∨-comm _ _ ⟩
    (y ∨ x) ∧ (z ∨ x)
                       ∎

  ∧-∨-distribʳ : _∧_ DistributesOverʳ _∨_
  ∧-∨-distribʳ x y z =
    (y ∨ z) ∧ x
                       ≃⟨ ∧-comm _ _ ⟩
    x ∧ (y ∨ z)
                       ≃⟨ ∧-∨-distrib _ _ _ ⟩
    (x ∧ y) ∨ (x ∧ z)
                       ≃⟨ ∧-comm _ _ ⟨ ∨-pres-≈ ⟩ ∧-comm _ _ ⟩
    (y ∧ x) ∨ (z ∧ x)
                       ∎

  ∨-complementˡ : LeftInverse ⊤ ¬_ _∨_
  ∨-complementˡ x =
    (¬ x) ∨ x
               ≃⟨ ∨-comm _ _ ⟩
    x ∨ (¬ x)
               ≃⟨ ∨-complement _ ⟩
    ⊤
               ∎

  ∧-complementˡ : LeftInverse ⊥ ¬_ _∧_
  ∧-complementˡ x =
    (¬ x) ∧ x
               ≃⟨ ∧-comm _ _ ⟩
    x ∧ (¬ x)
               ≃⟨ ∧-complement _ ⟩
    ⊥
               ∎

  ∧-identity : Identity ⊤ _∧_
  ∧-identity = (\_ -> ∧-comm _ _ ⟨ trans ⟩ x∧⊤=x _) , x∧⊤=x
    where
    x∧⊤=x : forall x -> (x ∧ ⊤) ≈ x
    x∧⊤=x x =
      x ∧ ⊤
                     ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (∨-complement _) ⟩
      x ∧ (x ∨ ¬ x)
                     ≃⟨ proj₂ absorptive _ _ ⟩
      x
                     ∎

  ∨-identity : Identity ⊥ _∨_
  ∨-identity = (\_ -> ∨-comm _ _ ⟨ trans ⟩ x∨⊥=x _) , x∨⊥=x
    where
    x∨⊥=x : forall x -> (x ∨ ⊥) ≈ x
    x∨⊥=x x =
      x ∨ ⊥
                     ≃⟨ byDef ⟨ ∨-pres-≈ ⟩ sym (∧-complement _) ⟩
      x ∨ (x ∧ ¬ x)
                     ≃⟨ proj₁ absorptive _ _ ⟩
      x
                     ∎

  ∧-zero : Zero ⊥ _∧_
  ∧-zero = (\_ -> ∧-comm _ _ ⟨ trans ⟩ x∧⊥=⊥ _) , x∧⊥=⊥
    where
    x∧⊥=⊥ : forall x -> (x ∧ ⊥) ≈ ⊥
    x∧⊥=⊥ x =
      x ∧ ⊥
                     ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (∧-complement _) ⟩
      x ∧ (x ∧ ¬ x)
                     ≃⟨ ∧-assoc _ _ _ ⟩
      (x ∧ x) ∧ ¬ x
                     ≃⟨ ∧-idempotent _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
      x ∧ ¬ x
                     ≃⟨ ∧-complement _ ⟩
      ⊥
                     ∎

  ∨-zero : Zero ⊤ _∨_
  ∨-zero = (\_ -> ∨-comm _ _ ⟨ trans ⟩ x∨⊤=⊤ _) , x∨⊤=⊤
    where
    x∨⊤=⊤ : forall x -> (x ∨ ⊤) ≈ ⊤
    x∨⊤=⊤ x =
      x ∨ ⊤
                     ≃⟨ byDef ⟨ ∨-pres-≈ ⟩ sym (∨-complement _) ⟩
      x ∨ (x ∨ ¬ x)
                     ≃⟨ ∨-assoc _ _ _ ⟩
      (x ∨ x) ∨ ¬ x
                     ≃⟨ ∨-idempotent _ ⟨ ∨-pres-≈ ⟩ byDef ⟩
      x ∨ ¬ x
                     ≃⟨ ∨-complement _ ⟩
      ⊤
                     ∎

  -- I took the statement of this lemma (called Uniqueness of
  -- Complements) from some course notes, "Boolean Algebra", written
  -- by Gert Smolka.

  private
    lemma : forall x y -> (x ∧ y) ≈ ⊥ -> (x ∨ y) ≈ ⊤ -> (¬ x) ≈ y
    lemma x y x∧y=⊥ x∨y=⊤ =
      (¬ x)
                                 ≃⟨ sym $ proj₂ ∧-identity _ ⟩
      (¬ x) ∧ ⊤
                                 ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ sym x∨y=⊤ ⟩
      (¬ x) ∧ (x ∨ y)
                                 ≃⟨ ∧-∨-distrib _ _ _ ⟩
      ((¬ x) ∧ x) ∨ ((¬ x) ∧ y)
                                 ≃⟨ ∧-complementˡ _ ⟨ ∨-pres-≈ ⟩ byDef ⟩
      ⊥ ∨ ((¬ x) ∧ y)
                                 ≃⟨ sym x∧y=⊥ ⟨ ∨-pres-≈ ⟩ byDef ⟩
      (x ∧ y) ∨ ((¬ x) ∧ y)
                                 ≃⟨ sym $ ∧-∨-distribʳ _ _ _ ⟩
      (x ∨ ¬ x) ∧ y
                                 ≃⟨ ∨-complement _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
      ⊤ ∧ y
                                 ≃⟨ proj₁ ∧-identity _ ⟩
      y
                                 ∎

  ¬⊥=⊤ : ¬ ⊥ ≈ ⊤
  ¬⊥=⊤ = lemma ⊥ ⊤ (proj₂ ∧-identity _) (proj₂ ∨-zero _)

  ¬⊤=⊥ : ¬ ⊤ ≈ ⊥
  ¬⊤=⊥ = lemma ⊤ ⊥ (proj₂ ∧-zero _) (proj₂ ∨-identity _)

  ¬-involutive : Involutive ¬_
  ¬-involutive x = lemma (¬ x) x (∧-complementˡ _) (∨-complementˡ _)

  deMorgan₁ : forall x y -> ¬ (x ∧ y) ≈ ((¬ x) ∨ (¬ y))
  deMorgan₁ x y = lemma (x ∧ y) ((¬ x) ∨ (¬ y)) lem₁ lem₂
    where
    lem₁ =
      (x ∧ y) ∧ ((¬ x) ∨ (¬ y))
                                             ≃⟨ ∧-∨-distrib _ _ _ ⟩
      ((x ∧ y) ∧ (¬ x)) ∨ ((x ∧ y) ∧ (¬ y))
                                             ≃⟨ ∧-comm _ _ ⟨ ∧-pres-≈ ⟩ byDef ⟨ ∨-pres-≈ ⟩ byDef ⟩
      ((y ∧ x) ∧ (¬ x)) ∨ ((x ∧ y) ∧ (¬ y))
                                             ≃⟨ sym (∧-assoc _ _ _) ⟨ ∨-pres-≈ ⟩ sym (∧-assoc _ _ _) ⟩
      (y ∧ (x ∧ (¬ x))) ∨ (x ∧ (y ∧ (¬ y)))
                                             ≃⟨ (byDef ⟨ ∧-pres-≈ ⟩ ∧-complement _) ⟨ ∨-pres-≈ ⟩
                                                (byDef ⟨ ∧-pres-≈ ⟩ ∧-complement _) ⟩
      (y ∧ ⊥) ∨ (x ∧ ⊥)
                                             ≃⟨ proj₂ ∧-zero _ ⟨ ∨-pres-≈ ⟩ proj₂ ∧-zero _ ⟩
      ⊥ ∨ ⊥
                                             ≃⟨ proj₂ ∨-identity _ ⟩
      ⊥
                                             ∎

    lem₃ =
      (x ∧ y) ∨ (¬ x)
                                 ≃⟨ ∨-∧-distribʳ _ _ _ ⟩
      (x ∨ (¬ x)) ∧ (y ∨ (¬ x))
                                 ≃⟨ ∨-complement _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
      ⊤ ∧ (y ∨ (¬ x))
                                 ≃⟨ proj₁ ∧-identity _ ⟩
      y ∨ (¬ x)
                                 ≃⟨ ∨-comm _ _ ⟩
      (¬ x) ∨ y
                                 ∎

    lem₂ =
      (x ∧ y) ∨ ((¬ x) ∨ (¬ y))
                                 ≃⟨ ∨-assoc _ _ _ ⟩
      ((x ∧ y) ∨ (¬ x)) ∨ (¬ y)
                                 ≃⟨ lem₃ ⟨ ∨-pres-≈ ⟩ byDef ⟩
      ((¬ x) ∨ y) ∨ (¬ y)
                                 ≃⟨ sym $ ∨-assoc _ _ _ ⟩
      (¬ x) ∨ (y ∨ (¬ y))
                                 ≃⟨ byDef ⟨ ∨-pres-≈ ⟩ ∨-complement _ ⟩
      (¬ x) ∨ ⊤
                                 ≃⟨ proj₂ ∨-zero _ ⟩
      ⊤
                                 ∎

  deMorgan₂ : forall x y -> ¬ (x ∨ y) ≈ ((¬ x) ∧ (¬ y))
  deMorgan₂ x y =
    ¬ (x ∨ y)
                           ≃⟨ ¬-pres-≈ $ sym (¬-involutive _) ⟨ ∨-pres-≈ ⟩
                                         sym (¬-involutive _) ⟩
    ¬ ((¬ ¬ x) ∨ (¬ ¬ y))
                           ≃⟨ ¬-pres-≈ $ sym $ deMorgan₁ _ _ ⟩
    ¬ ¬ ((¬ x) ∧ (¬ y))
                           ≃⟨ ¬-involutive _ ⟩
    (¬ x) ∧ (¬ y)
                           ∎
