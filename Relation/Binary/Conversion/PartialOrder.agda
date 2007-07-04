------------------------------------------------------------------------
-- Conversions between strict and non-strict partial orders
------------------------------------------------------------------------

module Relation.Binary.Conversion.PartialOrder where

open import Relation.Nullary
open import Relation.Binary
open import Data.Function
open import Logic
open import Data.Product
open import Data.Sum

-- TODO: Check if the following definitions are easier to work with:
--
-- x < y ⇔ ¬ (x ≥ y)
-- x ≤ y ⇔ ¬ (x > y)

------------------------------------------------------------------------
-- Conversions

-- Converts partial orders to strict partial orders (assuming that
-- they satisfy the right properties).

≤⟶< : forall {a} -> (≈ ≤ : Rel a) -> Rel a
≤⟶< _≈_ _≤_ = \x y -> (x ≤ y) × ¬ (x ≈ y)

-- Converts strict partial orders to partial orders (assuming that
-- they satisfy the right properties).

<⟶≤ : forall {a} -> (≈ < : Rel a) -> Rel a
<⟶≤ _≈_ _<_ = \x y -> (x < y) ⊎ (x ≈ y)

------------------------------------------------------------------------
-- The converted relations have certain properties
-- (if the original relations have certain other properties)

abstract

  irrefl-≤⟶< : forall {a} -> (≈ ≤ : Rel a) -> Irreflexive ≈ (≤⟶< ≈ ≤)
  irrefl-≤⟶< _ _ = \x≈y x<y -> proj₂ x<y x≈y

  refl-<⟶≤ : forall {a} -> (≈ < : Rel a) -> Reflexive ≈ (<⟶≤ ≈ <)
  refl-<⟶≤ _ _ = inj₂

  antisym-<⟶≤ :  forall {a} -> {≈ < : Rel a}
              -> Equivalence ≈
              -> Transitive <
              -> Irreflexive ≈ <
              -> Antisymmetric ≈ (<⟶≤ ≈ <)
  antisym-<⟶≤ {≈ = ≈} {< = <} eq trans irrefl = antisym
    where
    open module Eq  = Equivalence eq
    open module Pre = Preorder preorder

    antisym : Antisymmetric ≈ (<⟶≤ ≈ <)
    antisym (inj₂ x≈y) _          = x≈y
    antisym (inj₁ _)   (inj₂ y≈x) = sym y≈x
    antisym (inj₁ x<y) (inj₁ y<x) =
      ⊥-elim (trans∧irr⟶asym refl trans irrefl x<y y<x)

  trans-≤⟶< :  forall {a} -> {≈ ≤ : Rel a}
            -> PartialOrder ≈ ≤
            -> Transitive (≤⟶< ≈ ≤)
  trans-≤⟶< {≈ = _≈_} {≤ = _≤_} po = \x<y y<z ->
    trans (proj₁ x<y) (proj₁ y<z) ,
    \x≈z -> proj₂ x<y $ lemma (proj₁ x<y) (proj₁ y<z) x≈z
    where
    open module PO = PartialOrder po
    open module Po = Preorder preorder
    open module Eq = Equivalence equiv

    lemma : forall {x y z} -> x ≤ y -> y ≤ z -> x ≈ z -> x ≈ y
    lemma x≤y y≤z x≈z = antisym x≤y $ trans y≤z (refl $ sym x≈z)

  trans-<⟶≤
    :  forall {a} -> {≈ < : Rel a}
    -> Symmetric ≈ -> Transitive ≈ -> ≈ Respects₂ < -> Transitive <
    -> Transitive (<⟶≤ ≈ <)
  trans-<⟶≤ {≈ = ≈} {< = <} sym trans-≈ resp trans-< = trans
    where
    trans : Transitive (<⟶≤ ≈ <)
    trans (inj₁ x<y) (inj₁ y<z) = inj₁ $ trans-< x<y y<z
    trans (inj₁ x<y) (inj₂ y≈z) = inj₁ $ proj₁ resp y≈z x<y
    trans (inj₂ x≈y) (inj₁ y<z) = inj₁ $ proj₂ resp (sym x≈y) y<z
    trans (inj₂ x≈y) (inj₂ y≈z) = inj₂ $ trans-≈ x≈y y≈z

  total-≤⟶tri-<
    :  forall {a} -> {≈ ≤ : Rel a}
    -> Symmetric ≈ -> Decidable ≈
    -> Antisymmetric ≈ ≤ -> Total ≤
    -> Trichotomous ≈ (≤⟶< ≈ ≤)
  total-≤⟶tri-< {≈ = ≈} {≤ = ≤} sym dec antisym total = tri
    where
    < = ≤⟶< ≈ ≤

    irrefl : Irreflexive ≈ <
    irrefl = irrefl-≤⟶< ≈ ≤

    tri : Trichotomous ≈ <
    tri x y with dec x y
    tri x y | yes x≈y = Tri₂ (irrefl x≈y) x≈y (irrefl (sym x≈y))
    tri x y | no  x≉y with total x y
    tri x y | no  x≉y | inj₁ x≤y =
      Tri₁ (x≤y , x≉y) x≉y (x≉y ∘ antisym x≤y ∘ proj₁)
    tri x y | no  x≉y | inj₂ x≥y =
      Tri₃ (x≉y ∘ flip antisym x≥y ∘ proj₁) x≉y (x≥y , x≉y ∘ sym)

  resp-≤⟶<
    :  forall {a} -> {≈ ≤ : Rel a}
    -> Equivalence ≈ -> ≈ Respects₂ ≤ -> ≈ Respects₂ (≤⟶< ≈ ≤)
  resp-≤⟶< eq resp =
    (\{x y' y} y'≈y x<y' -> proj₁ resp y'≈y (proj₁ x<y') ,
                            \x≈y -> proj₂ x<y' (trans x≈y (sym y'≈y))) ,
    (\{y x' x} x'≈x x'<y -> proj₂ resp x'≈x (proj₁ x'<y) ,
                            \x≈y -> proj₂ x'<y (trans x'≈x x≈y))
    where
    open module Eq  = Equivalence eq
    open module Pre = Preorder preorder

  resp-<⟶≤
    :  forall {a} -> {≈ < : Rel a}
    -> Equivalence ≈ -> ≈ Respects₂ < -> ≈ Respects₂ (<⟶≤ ≈ <)
  resp-<⟶≤ {≈ = _≈_} {< = <} eq resp =
    (\{_ _ _} -> resp₁) ,
    (\{_ _ _} -> resp₂)
    where
    open module Eq  = Equivalence eq
    open module Pre = Preorder preorder

    _≤_ = <⟶≤ _≈_ <

    resp₁ : forall {x y' y} -> y' ≈ y -> x  ≤ y' -> x ≤ y
    resp₁ y'≈y (inj₁ x<y') = inj₁ (proj₁ resp y'≈y x<y')
    resp₁ y'≈y (inj₂ x≈y') = inj₂ (trans x≈y' y'≈y)

    resp₂ : forall {y x' x} -> x' ≈ x -> x' ≤ y  -> x ≤ y
    resp₂ x'≈x (inj₁ x'<y) = inj₁ (proj₂ resp x'≈x x'<y)
    resp₂ x'≈x (inj₂ x'≈y) = inj₂ (trans (sym x'≈x) x'≈y)

  decidable-≤⟶<
    :  forall {a} -> {≈ ≤ : Rel a}
    -> Decidable ≈ -> Decidable ≤ -> Decidable (≤⟶< ≈ ≤)
  decidable-≤⟶< {≈ = ≈} {≤ = ≤} dec-≈ dec-≤ = dec
    where
    dec : Decidable (≤⟶< ≈ ≤)
    dec x y with dec-≈ x y | dec-≤ x y
    dec x y | yes x≈y | _       = no (flip proj₂ x≈y)
    dec x y | no  x≉y | yes x≤y = yes (x≤y , x≉y)
    dec x y | no  x≉y | no  x≰y = no (x≰y ∘ proj₁)

  decidable-<⟶≤
    :  forall {a} -> {≈ < : Rel a}
    -> Decidable ≈ -> Decidable < -> Decidable (<⟶≤ ≈ <)
  decidable-<⟶≤ {≈ = ≈} {< = <} dec-≈ dec-< = dec
    where
    _≤_ = <⟶≤ ≈ <

    dec : Decidable _≤_
    dec x y with dec-≈ x y | dec-< x y
    dec x y | yes x≈y | _       = yes (inj₂ x≈y)
    dec x y | no  x≉y | yes x<y = yes (inj₁ x<y)
    dec x y | no  x≉y | no  x≮y = no helper
      where
      helper : x ≤ y -> ⊥
      helper (inj₁ x<y) = x≮y x<y
      helper (inj₂ x≈y) = x≉y x≈y

  po⟶spo :  forall {a} -> {≈ ≤ : Rel a}
         -> PartialOrder ≈ ≤ -> StrictPartialOrder ≈ (≤⟶< ≈ ≤)
  po⟶spo {≈ = _≈_} {≤ = _≤_} po = record
    { equiv    = equiv
    ; irrefl   = irrefl-≤⟶< _≈_ _≤_
    ; trans    = trans-≤⟶< po
    ; ≈-resp-< = resp-≤⟶< equiv ≈-resp-≤
    }
    where
    open module PO = PartialOrder po

  spo⟶po :  forall {a} -> {≈ < : Rel a}
         -> ≈ Respects₂ < -> StrictPartialOrder ≈ <
         -> PartialOrder ≈ (<⟶≤ ≈ <)
  spo⟶po {≈ = ≈} {< = <} resp spo = record
    { equiv    = equiv
    ; preorder = record
        { refl    = refl-<⟶≤ ≈ <
        ; trans   = trans-<⟶≤ {< = <} Eq.sym Pre.trans resp trans
        }
    ; antisym  = antisym-<⟶≤ equiv trans irrefl
    ; ≈-resp-≤ = resp-<⟶≤ equiv ≈-resp-<
    }
    where
    open module SPO = StrictPartialOrder spo
    module Eq  = Equivalence equiv
    module Pre = Preorder Eq.preorder
