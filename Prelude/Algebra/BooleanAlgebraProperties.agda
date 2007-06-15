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

module BoolAlgRing
  (_⊕_ : Op₂)
  (⊕-def : forall x y -> (x ⊕ y) ≈ ((x ∨ y) ∧ ¬ (x ∧ y)))
  where

  abstract
    private
      helper :  forall {x y u v}
             -> x ≈ y -> u ≈ v -> (x ∧ ¬ u) ≈ (y ∧ ¬ v)
      helper x≈y u≈v = x≈y ⟨ ∧-pres-≈ ⟩ ¬-pres-≈ u≈v

    ⊕-¬-distribˡ : forall x y -> ¬ (x ⊕ y) ≈ ((¬ x) ⊕ y)
    ⊕-¬-distribˡ x y =
      ¬ (x ⊕ y)
                                             ≃⟨ ¬-pres-≈ $ ⊕-def _ _ ⟩
      ¬ ((x ∨ y) ∧ (¬ (x ∧ y)))
                                             ≃⟨ ¬-pres-≈ (∧-∨-distribʳ _ _ _) ⟩
      ¬ ((x ∧ ¬ (x ∧ y)) ∨ (y ∧ ¬ (x ∧ y)))
                                             ≃⟨ ¬-pres-≈ $
                                                  byDef ⟨ ∨-pres-≈ ⟩
                                                    (byDef ⟨ ∧-pres-≈ ⟩
                                                       ¬-pres-≈ (∧-comm _ _)) ⟩
      ¬ ((x ∧ ¬ (x ∧ y)) ∨ (y ∧ ¬ (y ∧ x)))
                                             ≃⟨ ¬-pres-≈ $ lem _ _ ⟨ ∨-pres-≈ ⟩ lem _ _ ⟩
      ¬ ((x ∧ ¬ y) ∨ (y ∧ ¬ x))
                                             ≃⟨ deMorgan₂ _ _ ⟩
      (¬ (x ∧ ¬ y) ∧ ¬ (y ∧ ¬ x))
                                             ≃⟨ deMorgan₁ _ _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
      (((¬ x) ∨ (¬ ¬ y)) ∧ ¬ (y ∧ ¬ x))
                                             ≃⟨ helper (byDef ⟨ ∨-pres-≈ ⟩ ¬-involutive _)
                                                  (∧-comm _ _) ⟩
      (((¬ x) ∨ y) ∧ ¬ ((¬ x) ∧ y))
                                             ≃⟨ sym $ ⊕-def _ _ ⟩
      ((¬ x) ⊕ y)
                                             ∎
      where
      lem : forall x y -> (x ∧ ¬ (x ∧ y)) ≈ (x ∧ (¬ y))
      lem x y =
        x ∧ ¬ (x ∧ y)
                                   ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ deMorgan₁ _ _ ⟩
        x ∧ ((¬ x) ∨ (¬ y))
                                   ≃⟨ ∧-∨-distrib _ _ _ ⟩
        (x ∧ (¬ x)) ∨ (x ∧ (¬ y))
                                   ≃⟨ ∧-complement _ ⟨ ∨-pres-≈ ⟩ byDef ⟩
        ⊥ ∨ (x ∧ (¬ y))
                                   ≃⟨ proj₁ ∨-identity _ ⟩
        x ∧ (¬ y)
                                   ∎

    private
      ⊕-comm : Commutative _⊕_
      ⊕-comm x y =
        x ⊕ y
                             ≃⟨ ⊕-def _ _ ⟩
        (x ∨ y) ∧ ¬ (x ∧ y)
                             ≃⟨ helper (∨-comm _ _) (∧-comm _ _) ⟩
        (y ∨ x) ∧ ¬ (y ∧ x)
                             ≃⟨ sym $ ⊕-def _ _ ⟩
        y ⊕ x
                             ∎

    ⊕-¬-distribʳ : forall x y -> ¬ (x ⊕ y) ≈ (x ⊕ (¬ y))
    ⊕-¬-distribʳ x y =
      ¬ (x ⊕ y)
                   ≃⟨ ¬-pres-≈ $ ⊕-comm _ _ ⟩
      ¬ (y ⊕ x)
                   ≃⟨ ⊕-¬-distribˡ _ _ ⟩
      ((¬ y) ⊕ x)
                   ≃⟨ ⊕-comm _ _ ⟩
      (x ⊕ (¬ y))
                   ∎

    ⊕-annihilates-¬ : forall x y -> (x ⊕ y) ≈ ((¬ x) ⊕ (¬ y))
    ⊕-annihilates-¬ x y =
      x ⊕ y
                       ≃⟨ sym $ ¬-involutive _ ⟩
      ¬ ¬ (x ⊕ y)
                       ≃⟨ ¬-pres-≈ $ ⊕-¬-distribˡ _ _ ⟩
      ¬ ((¬ x) ⊕ y)
                       ≃⟨ ⊕-¬-distribʳ _ _ ⟩
      ((¬ x) ⊕ (¬ y))
                       ∎

    private
      ⊕-pres : _⊕_ Preserves₂-≈
      ⊕-pres {x} {y} {u} {v} x≈y u≈v =
        x ⊕ u
                             ≃⟨ ⊕-def _ _ ⟩
        (x ∨ u) ∧ ¬ (x ∧ u)
                             ≃⟨ helper (x≈y ⟨ ∨-pres-≈ ⟩ u≈v)
                                       (x≈y ⟨ ∧-pres-≈ ⟩ u≈v) ⟩
        (y ∨ v) ∧ ¬ (y ∧ v)
                             ≃⟨ sym $ ⊕-def _ _ ⟩
        y ⊕ v
                             ∎

      ⊕-identity : Identity ⊥ _⊕_
      ⊕-identity = ⊥⊕x=x , (\_ -> ⊕-comm _ _ ⟨ trans ⟩ ⊥⊕x=x _)
        where
        ⊥⊕x=x : forall x -> (⊥ ⊕ x) ≈ x
        ⊥⊕x=x x =
          ⊥ ⊕ x
                               ≃⟨ ⊕-def _ _ ⟩
          (⊥ ∨ x) ∧ ¬ (⊥ ∧ x)
                               ≃⟨ helper (proj₁ ∨-identity _)
                                         (proj₁ ∧-zero _) ⟩
          x ∧ ¬ ⊥
                               ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ ¬⊥=⊤ ⟩
          x ∧ ⊤
                               ≃⟨ proj₂ ∧-identity _ ⟩
          x
                               ∎

      ⊕-inverse : Inverse ⊥ id _⊕_
      ⊕-inverse = x⊕x=⊥ , (\_ -> ⊕-comm _ _ ⟨ trans ⟩ x⊕x=⊥ _)
        where
        x⊕x=⊥ : forall x -> (x ⊕ x) ≈ ⊥
        x⊕x=⊥ x =
          x ⊕ x
                               ≃⟨ ⊕-def _ _ ⟩
          (x ∨ x) ∧ ¬ (x ∧ x)
                               ≃⟨ helper (∨-idempotent _)
                                         (∧-idempotent _) ⟩
          x ∧ ¬ x
                               ≃⟨ ∧-complement _ ⟩
          ⊥
                               ∎

      distrib-∧-⊕ : _∧_ DistributesOver _⊕_
      distrib-∧-⊕ = distˡ , distʳ
        where
        distˡ : _∧_ DistributesOverˡ _⊕_
        distˡ x y z =
          x ∧ (y ⊕ z)
                                     ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ ⊕-def _ _ ⟩
          x ∧ ((y ∨ z) ∧ ¬ (y ∧ z))
                                     ≃⟨ ∧-assoc _ _ _ ⟩
          (x ∧ (y ∨ z)) ∧ ¬ (y ∧ z)
                                     ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ deMorgan₁ _ _ ⟩
          (x ∧ (y ∨ z)) ∧
          ((¬ y) ∨ (¬ z))
                                     ≃⟨ sym $ proj₁ ∨-identity _ ⟩
          ⊥ ∨
          ((x ∧ (y ∨ z)) ∧
           ((¬ y) ∨ (¬ z)))
                                     ≃⟨ lem₃ ⟨ ∨-pres-≈ ⟩ byDef ⟩
          ((x ∧ (y ∨ z)) ∧ (¬ x)) ∨
          ((x ∧ (y ∨ z)) ∧
           ((¬ y) ∨ (¬ z)))
                                     ≃⟨ sym $ ∧-∨-distrib _ _ _ ⟩
          (x ∧ (y ∨ z)) ∧
          ((¬ x) ∨ ((¬ y) ∨ (¬ z)))
                                     ≃⟨  byDef ⟨ ∧-pres-≈ ⟩
                                        (byDef ⟨ ∨-pres-≈ ⟩ sym (deMorgan₁ _ _)) ⟩
          (x ∧ (y ∨ z)) ∧
          ((¬ x) ∨ ¬ (y ∧ z))
                                     ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (deMorgan₁ _ _) ⟩
            (x ∧ (y ∨ z)) ∧
          ¬ (x ∧ (y ∧ z))
                                     ≃⟨ helper byDef lem₁ ⟩
            (x ∧ (y ∨ z)) ∧
          ¬ ((x ∧ y) ∧ (x ∧ z))
                                     ≃⟨ ∧-∨-distrib _ _ _ ⟨ ∧-pres-≈ ⟩
                                        byDef ⟩
            ((x ∧ y) ∨ (x ∧ z)) ∧
          ¬ ((x ∧ y) ∧ (x ∧ z))
                                     ≃⟨ sym $ ⊕-def _ _ ⟩
          (x ∧ y) ⊕ (x ∧ z)
                                     ∎
          where
          lem₂ =
            x ∧ (y ∧ z)
                         ≃⟨ ∧-assoc _ _ _ ⟩
            (x ∧ y) ∧ z
                         ≃⟨ ∧-comm _ _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
            (y ∧ x) ∧ z
                         ≃⟨ sym $ ∧-assoc _ _ _ ⟩
            y ∧ (x ∧ z)
                         ∎

          lem₁ =
            x ∧ (y ∧ z)
                               ≃⟨ sym (∧-idempotent _) ⟨ ∧-pres-≈ ⟩ byDef ⟩
            (x ∧ x) ∧ (y ∧ z)
                               ≃⟨ sym $ ∧-assoc _ _ _ ⟩
            x ∧ (x ∧ (y ∧ z))
                               ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ lem₂ ⟩
            x ∧ (y ∧ (x ∧ z))
                               ≃⟨ ∧-assoc _ _ _ ⟩
            (x ∧ y) ∧ (x ∧ z)
                               ∎

          lem₃ =
            ⊥
                                   ≃⟨ sym $ proj₂ ∧-zero _ ⟩
            (y ∨ z) ∧ ⊥
                                   ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (∧-complement _) ⟩
            (y ∨ z) ∧ (x ∧ (¬ x))
                                   ≃⟨ ∧-assoc _ _ _ ⟩
            ((y ∨ z) ∧ x) ∧ (¬ x)
                                   ≃⟨ ∧-comm _ _ ⟨ ∧-pres-≈ ⟩ byDef  ⟩
            (x ∧ (y ∨ z)) ∧ (¬ x)
                                   ∎

        distʳ : _∧_ DistributesOverʳ _⊕_
        distʳ x y z =
          (y ⊕ z) ∧ x
                             ≃⟨ ∧-comm _ _ ⟩
          x ∧ (y ⊕ z)
                             ≃⟨ distˡ _ _ _ ⟩
          (x ∧ y) ⊕ (x ∧ z)
                             ≃⟨ ∧-comm _ _ ⟨ ⊕-pres ⟩ ∧-comm _ _ ⟩
          (y ∧ x) ⊕ (z ∧ x)
                             ∎

      lemma₂ :  forall x y u v
             -> ((x ∧ y) ∨ (u ∧ v)) ≈
                (((x ∨ u) ∧ (y ∨ u)) ∧
                 ((x ∨ v) ∧ (y ∨ v)))
      lemma₂ x y u v =
          (x ∧ y) ∨ (u ∧ v)
        ≃⟨ ∨-∧-distrib _ _ _ ⟩
          ((x ∧ y) ∨ u) ∧ ((x ∧ y) ∨ v)
        ≃⟨ ∨-∧-distribʳ _ _ _ ⟨ ∧-pres-≈ ⟩ ∨-∧-distribʳ _ _ _ ⟩
          ((x ∨ u) ∧ (y ∨ u)) ∧ ((x ∨ v) ∧ (y ∨ v))
        ∎

      ⊕-assoc : Associative _⊕_
      ⊕-assoc x y z =
        x ⊕ (y ⊕ z)
                                                            ≃⟨ byDef ⟨ ⊕-pres ⟩ ⊕-def _ _ ⟩
        x ⊕ ((y ∨ z) ∧ ¬ (y ∧ z))
                                                            ≃⟨ ⊕-def _ _ ⟩
          (x ∨ ((y ∨ z) ∧ ¬ (y ∧ z))) ∧
        ¬ (x ∧ ((y ∨ z) ∧ ¬ (y ∧ z)))
                                                            ≃⟨ lem₃ ⟨ ∧-pres-≈ ⟩ lem₄ ⟩
        (((x ∨ y) ∨ z) ∧ ((x ∨ (¬ y)) ∨ (¬ z))) ∧
        ((((¬ x) ∨ (¬ y)) ∨ z) ∧ (((¬ x) ∨ y) ∨ (¬ z)))
                                                            ≃⟨ sym $ ∧-assoc _ _ _ ⟩
        ((x ∨ y) ∨ z) ∧
        (((x ∨ (¬ y)) ∨ (¬ z)) ∧
         ((((¬ x) ∨ (¬ y)) ∨ z) ∧ (((¬ x) ∨ y) ∨ (¬ z))))
                                                            ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ lem₅ ⟩
        ((x ∨ y) ∨ z) ∧
        ((((¬ x) ∨ (¬ y)) ∨ z) ∧
         (((x ∨ (¬ y)) ∨ ¬ z) ∧ (((¬ x) ∨ y) ∨ ¬ z)))
                                                            ≃⟨ ∧-assoc _ _ _ ⟩
        (((x ∨ y) ∨ z) ∧ (((¬ x) ∨ (¬ y)) ∨ z)) ∧
        (((x ∨ (¬ y)) ∨ ¬ z) ∧ (((¬ x) ∨ y) ∨ ¬ z))
                                                            ≃⟨ lem₁ ⟨ ∧-pres-≈ ⟩ lem₂ ⟩
          (((x ∨ y) ∧ ¬ (x ∧ y)) ∨ z) ∧
        ¬ (((x ∨ y) ∧ ¬ (x ∧ y)) ∧ z)
                                                            ≃⟨ sym $ ⊕-def _ _ ⟩
        ((x ∨ y) ∧ ¬ (x ∧ y)) ⊕ z
                                                            ≃⟨ sym $ ⊕-def _ _ ⟨ ⊕-pres ⟩ byDef ⟩
        (x ⊕ y) ⊕ z
                                                            ∎
        where
        lem₁ =
          ((x ∨ y) ∨ z) ∧ (((¬ x) ∨ (¬ y)) ∨ z)
                                                 ≃⟨ sym $ ∨-∧-distribʳ _ _ _ ⟩
          ((x ∨ y) ∧ ((¬ x) ∨ (¬ y))) ∨ z
                                                 ≃⟨ byDef ⟨ ∧-pres-≈ ⟩ sym (deMorgan₁ _ _)
                                                      ⟨ ∨-pres-≈ ⟩ byDef ⟩
          ((x ∨ y) ∧ ¬ (x ∧ y)) ∨ z
                                                 ∎

        lem₂' =
          (x ∨ (¬ y)) ∧ ((¬ x) ∨ y)
                                                 ≃⟨ sym $
                                                      proj₁ ∧-identity _
                                                        ⟨ ∧-pres-≈ ⟩
                                                      proj₂ ∧-identity _ ⟩
          (⊤ ∧ (x ∨ (¬ y))) ∧ (((¬ x) ∨ y) ∧ ⊤)
                                                 ≃⟨ sym $
                                                      (∨-complementˡ _ ⟨ ∧-pres-≈ ⟩ ∨-comm _ _)
                                                        ⟨ ∧-pres-≈ ⟩
                                                      (byDef ⟨ ∧-pres-≈ ⟩ ∨-complementˡ _) ⟩
          (((¬ x) ∨ x) ∧ ((¬ y) ∨ x)) ∧
          (((¬ x) ∨ y) ∧ ((¬ y) ∨ y))
                                                 ≃⟨ sym $ lemma₂ _ _ _ _ ⟩
          ((¬ x) ∧ (¬ y)) ∨ (x ∧ y)
                                                 ≃⟨ sym $ deMorgan₂ _ _ ⟨ ∨-pres-≈ ⟩ ¬-involutive _ ⟩
          ¬ (x ∨ y) ∨ ¬ ¬ (x ∧ y)
                                                 ≃⟨ sym (deMorgan₁ _ _) ⟩
          ¬ ((x ∨ y) ∧ ¬ (x ∧ y))
                                                 ∎

        lem₂ =
          ((x ∨ (¬ y)) ∨ ¬ z) ∧ (((¬ x) ∨ y) ∨ ¬ z)
                                                     ≃⟨ sym $ ∨-∧-distribʳ _ _ _ ⟩
          ((x ∨ (¬ y)) ∧ ((¬ x) ∨ y)) ∨ ¬ z
                                                     ≃⟨ lem₂' ⟨ ∨-pres-≈ ⟩ byDef ⟩
          ¬ ((x ∨ y) ∧ ¬ (x ∧ y)) ∨ ¬ z
                                                     ≃⟨ sym $ deMorgan₁ _ _ ⟩
          ¬ (((x ∨ y) ∧ ¬ (x ∧ y)) ∧ z)
                                                     ∎

        lem₃ =
          x ∨ ((y ∨ z) ∧ ¬ (y ∧ z))
                                                 ≃⟨ byDef ⟨ ∨-pres-≈ ⟩
                                                      (byDef ⟨ ∧-pres-≈ ⟩ deMorgan₁ _ _) ⟩
          x ∨ ((y ∨ z) ∧ ((¬ y) ∨ (¬ z)))
                                                 ≃⟨ ∨-∧-distrib _ _ _ ⟩
          (x ∨ (y ∨ z)) ∧ (x ∨ ((¬ y) ∨ (¬ z)))
                                                 ≃⟨ ∨-assoc _ _ _ ⟨ ∧-pres-≈ ⟩ ∨-assoc _ _ _ ⟩
          ((x ∨ y) ∨ z) ∧ ((x ∨ (¬ y)) ∨ (¬ z))
                                                 ∎

        lem₄' =
          ¬ ((y ∨ z) ∧ ¬ (y ∧ z))
                                         ≃⟨ deMorgan₁ _ _ ⟩
          ¬ (y ∨ z) ∨ ¬ ¬ (y ∧ z)
                                         ≃⟨ deMorgan₂ _ _ ⟨ ∨-pres-≈ ⟩ ¬-involutive _ ⟩
          ((¬ y) ∧ (¬ z)) ∨ (y ∧ z)
                                         ≃⟨ lemma₂ _ _ _ _ ⟩
          (((¬ y) ∨ y) ∧ ((¬ z) ∨ y)) ∧
          (((¬ y) ∨ z) ∧ ((¬ z) ∨ z))
                                         ≃⟨ (∨-complementˡ _ ⟨ ∧-pres-≈ ⟩ ∨-comm _ _)
                                              ⟨ ∧-pres-≈ ⟩
                                            (byDef ⟨ ∧-pres-≈ ⟩ ∨-complementˡ _) ⟩
          (⊤ ∧ (y ∨ (¬ z))) ∧
          (((¬ y) ∨ z) ∧ ⊤)
                                         ≃⟨ proj₁ ∧-identity _ ⟨ ∧-pres-≈ ⟩
                                            proj₂ ∧-identity _ ⟩
          (y ∨ (¬ z)) ∧ ((¬ y) ∨ z)
                                         ∎

        lem₄ =
          ¬ (x ∧ ((y ∨ z) ∧ ¬ (y ∧ z)))
                                                  ≃⟨ deMorgan₁ _ _ ⟩
          (¬ x) ∨ ¬ ((y ∨ z) ∧ ¬ (y ∧ z))
                                                  ≃⟨ byDef ⟨ ∨-pres-≈ ⟩ lem₄' ⟩
          (¬ x) ∨ ((y ∨ (¬ z)) ∧ ((¬ y) ∨ z))
                                                  ≃⟨ ∨-∧-distrib _ _ _ ⟩
          ((¬ x) ∨ (y     ∨ (¬ z))) ∧
          ((¬ x) ∨ ((¬ y) ∨ z))
                                                  ≃⟨ ∨-assoc _ _ _ ⟨ ∧-pres-≈ ⟩ ∨-assoc _ _ _ ⟩
          (((¬ x) ∨ y)     ∨ (¬ z)) ∧
          (((¬ x) ∨ (¬ y)) ∨ z)
                                                  ≃⟨ ∧-comm _ _ ⟩
          (((¬ x) ∨ (¬ y)) ∨ z) ∧
          (((¬ x) ∨ y)     ∨ (¬ z))
                                                  ∎

        lem₅ =
          ((x ∨ (¬ y)) ∨ (¬ z)) ∧
          ((((¬ x) ∨ (¬ y)) ∨ z) ∧ (((¬ x) ∨ y) ∨ (¬ z)))
                                                             ≃⟨ ∧-assoc _ _ _ ⟩
          (((x ∨ (¬ y)) ∨ (¬ z)) ∧ (((¬ x) ∨ (¬ y)) ∨ z)) ∧
          (((¬ x) ∨ y) ∨ (¬ z))
                                                             ≃⟨ ∧-comm _ _ ⟨ ∧-pres-≈ ⟩ byDef ⟩
          ((((¬ x) ∨ (¬ y)) ∨ z) ∧ ((x ∨ (¬ y)) ∨ (¬ z))) ∧
          (((¬ x) ∨ y) ∨ (¬ z))
                                                             ≃⟨ sym $ ∧-assoc _ _ _ ⟩
          (((¬ x) ∨ (¬ y)) ∨ z) ∧
          (((x ∨ (¬ y)) ∨ ¬ z) ∧ (((¬ x) ∨ y) ∨ ¬ z))
                                                             ∎

    ring : Ring _⊕_ _∧_ id ⊥ ⊤
    ring = record
      { +-group = record
        { group = record
          { monoid = record
            { semigroup = record
              { assoc    = ⊕-assoc
              ; •-pres-≈ = ⊕-pres
              }
            ; identity = ⊕-identity
            }
          ; inverse   = ⊕-inverse
          ; ⁻¹-pres-≈ = id
          }
        ; comm = ⊕-comm
        }
      ; *-monoid = record
        { semigroup = record
          { assoc    = ∧-assoc
          ; •-pres-≈ = ∧-pres-≈
          }
        ; identity = ∧-identity
        }
      ; distrib = distrib-∧-⊕
      }

  ringoid : Ringoid
  ringoid = record
    { setoid = setoid
    ; _+_    = _⊕_
    ; _*_    = _∧_
    ; -_     = id
    ; 0#     = ⊥
    ; 1#     = ⊤
    ; ring   = ring
    }

_⊕_ : Op₂
x ⊕ y = (x ∨ y) ∧ ¬ (x ∧ y)

module DefaultRing = BoolAlgRing _⊕_ (\_ _ -> byDef)
