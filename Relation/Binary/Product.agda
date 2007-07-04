------------------------------------------------------------------------
-- Products of binary relations
------------------------------------------------------------------------

module Relation.Binary.Product where

open import Logic
open import Data.Function
open import Data.Product
open import Data.Sum
open import Relation.Nullary.Product
open import Relation.Nullary.Sum
open import Relation.Binary
open import Relation.Binary.Conversion.PartialOrder

infixr 2 _×-Rel_

------------------------------------------------------------------------
-- Products of relations

-- Pointwise product.

_×-Rel_ : forall {a b} -> Rel a -> Rel b -> Rel (a × b)
∼₁ ×-Rel ∼₂ = (∼₁ on₁ proj₁) -×- (∼₂ on₁ proj₂)

-- Lexicographic products.

×-Lex :  forall {a₁} -> (≈₁ <₁ : Rel a₁)
      -> forall {a₂} -> (≤₂ : Rel a₂)
      -> Rel (a₁ × a₂)
×-Lex ≈₁ <₁ ≤₂ = (<₁ on₁ proj₁) -⊎- (≈₁ on₁ proj₁) -×- (≤₂ on₁ proj₂)

×-Lex-≤ :  forall {a₁} -> (≈₁ ≤₁ : Rel a₁)
        -> forall {a₂} -> (≤₂ : Rel a₂)
        -> Rel (a₁ × a₂)
×-Lex-≤ ≈₁ ≤₁ ≤₂ = ×-Lex ≈₁ (≤⟶< ≈₁ ≤₁) ≤₂

------------------------------------------------------------------------
-- Some properties are preserved

abstract

  _×-reflexive_
    :  forall {a₁} -> {≈₁ ∼₁ : Rel a₁} -> Reflexive ≈₁ ∼₁
    -> forall {a₂} -> {≈₂ ∼₂ : Rel a₂} -> Reflexive ≈₂ ∼₂
    -> Reflexive (≈₁ ×-Rel ≈₂) (∼₁ ×-Rel ∼₂)
  refl₁ ×-reflexive refl₂ = \x≈y -> refl₁ (proj₁ x≈y) , refl₂ (proj₂ x≈y)

  _×-reflexive-≡_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Reflexive _≡_ ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Reflexive _≡_ ∼₂
    -> Reflexive _≡_ (∼₁ ×-Rel ∼₂)
  (refl₁ ×-reflexive-≡ refl₂) ≡-refl = refl₁ ≡-refl , refl₂ ≡-refl

  ×-lex-reflexive
    :  forall {a₁} -> (≈₁ ∼₁ : Rel a₁)
    -> forall {a₂} -> {≈₂ : Rel a₂} -> forall ≤₂ -> Reflexive ≈₂ ≤₂
    -> Reflexive (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ ∼₁ ≤₂)
  ×-lex-reflexive _ _ _ refl₂ = \x≈y ->
    inj₂ (proj₁ x≈y , refl₂ (proj₂ x≈y))

  ×-lex-≤-reflexive
    :  forall {a₁} -> (≈₁ ≤₁ : Rel a₁)
    -> forall {a₂} -> {≈₂ : Rel a₂} -> forall ≤₂ -> Reflexive ≈₂ ≤₂
    -> Reflexive (≈₁ ×-Rel ≈₂) (×-Lex-≤ ≈₁ ≤₁ ≤₂)
  ×-lex-≤-reflexive ≈₁ ≤₁ ≤₂ refl₂ {x} {y} =
    ×-lex-reflexive ≈₁ (≤⟶< ≈₁ ≤₁) ≤₂ refl₂ {x} {y}

  ×-irreflexive₁
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁} -> Irreflexive ≈₁ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂}
    -> Irreflexive (≈₁ ×-Rel ≈₂) (<₁ ×-Rel <₂)
  ×-irreflexive₁ ir = \x≈y x<y -> ir (proj₁ x≈y) (proj₁ x<y)

  ×-irreflexive₂
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁}
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂} -> Irreflexive ≈₂ <₂
    -> Irreflexive (≈₁ ×-Rel ≈₂) (<₁ ×-Rel <₂)
  ×-irreflexive₂ ir = \x≈y x<y -> ir (proj₂ x≈y) (proj₂ x<y)

  _×-lex-irreflexive_
    :  forall {a₁} -> {≈₁ : Rel a₁} -> forall <₁ -> Irreflexive ≈₁ <₁
    -> forall {a₂} -> {≈₂ : Rel a₂} -> forall <₂ -> Irreflexive ≈₂ <₂
    -> Irreflexive (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ <₁ <₂)
  _×-lex-irreflexive_ {≈₁ = ≈₁} <₁ ir₁ {≈₂ = ≈₂} <₂ ir₂ {x} {y} =
    irrefl {x} {y}
    where
    irrefl : Irreflexive (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ <₁ <₂)
    irrefl x≈y (inj₁ x₁<y₁) = ir₁ (proj₁ x≈y) x₁<y₁
    irrefl x≈y (inj₂ x≈<y)  = ir₂ (proj₂ x≈y) (proj₂ x≈<y)

  _×-symmetric_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Symmetric ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Symmetric ∼₂
    -> Symmetric (∼₁ ×-Rel ∼₂)
  sym₁ ×-symmetric sym₂ = \x∼y -> sym₁ (proj₁ x∼y) , sym₂ (proj₂ x∼y)

  _×-transitive_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Transitive ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Transitive ∼₂
    -> Transitive (∼₁ ×-Rel ∼₂)
  trans₁ ×-transitive trans₂ = \x∼y y∼z ->
    trans₁ (proj₁ x∼y) (proj₁ y∼z) ,
    trans₂ (proj₂ x∼y) (proj₂ y∼z)

  ×-lex-transitive
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁}
    -> Equivalence ≈₁ -> ≈₁ Respects₂ <₁ -> Transitive <₁
    -> forall {a₂} -> {≤₂ : Rel a₂}
    -> Transitive ≤₂
    -> Transitive (×-Lex ≈₁ <₁ ≤₂)
  ×-lex-transitive {≈₁ = ≈₁} {<₁ = <₁} eq₁ resp₁ trans₁
                   {≤₂ = ≤₂} trans₂ {x} {y} {z} = trans {x} {y} {z}
    where
    trans : Transitive (×-Lex ≈₁ <₁ ≤₂)
    trans (inj₁ x₁<y₁) (inj₁ y₁<z₁) = inj₁ (trans₁ x₁<y₁ y₁<z₁)
    trans (inj₁ x₁<y₁) (inj₂ y≈≤z)  =
      inj₁ (proj₁ resp₁ (proj₁ y≈≤z) x₁<y₁)
    trans (inj₂ x≈≤y)  (inj₁ y₁<z₁) =
      inj₁ (proj₂ resp₁ (sym₁ $ proj₁ x≈≤y) y₁<z₁)
      where sym₁ = Equivalence.sym eq₁
    trans (inj₂ x≈≤y)  (inj₂ y≈≤z)  =
      inj₂ ( trans-≈₁ (proj₁ x≈≤y) (proj₁ y≈≤z)
           , trans₂ (proj₂ x≈≤y) (proj₂ y≈≤z) )
      where trans-≈₁ = Preorder.trans (Equivalence.preorder eq₁)

  ×-lex-≤-transitive
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁}
    -> PartialOrder ≈₁ ≤₁
    -> forall {a₂} -> {≤₂ : Rel a₂}
    -> Transitive ≤₂
    -> Transitive (×-Lex-≤ ≈₁ ≤₁ ≤₂)
  ×-lex-≤-transitive {≈₁ = ≈₁} {≤₁ = ≤₁} po₁ {≤₂ = ≤₂} trans₂
                     {x} {y} {z} =
    ×-lex-transitive
      {<₁ = ≤⟶< ≈₁ ≤₁} equiv (resp-≤⟶< equiv ≈-resp-≤) (trans-≤⟶< po₁)
      {≤₂ = ≤₂} trans₂ {x} {y} {z}
    where
    open module PO = PartialOrder po₁

  _×-antisymmetric_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁}
    -> Antisymmetric ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂}
    -> Antisymmetric ≈₂ ≤₂
    -> Antisymmetric (≈₁ ×-Rel ≈₂) (≤₁ ×-Rel ≤₂)
  antisym₁ ×-antisymmetric antisym₂ = \x≤y y≤x ->
    antisym₁ (proj₁ x≤y) (proj₁ y≤x) ,
    antisym₂ (proj₂ x≤y) (proj₂ y≤x)

  ×-lex-antisymmetric
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁}
    -> Symmetric ≈₁ -> Irreflexive ≈₁ <₁ -> Asymmetric <₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂}
    -> Antisymmetric ≈₂ ≤₂
    -> Antisymmetric (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ <₁ ≤₂)
  ×-lex-antisymmetric {≈₁ = ≈₁} {<₁ = <₁} sym₁ irrefl₁ asym₁
                      {≈₂ = ≈₂} {≤₂ = ≤₂} antisym₂ {x} {y} =
    antisym {x} {y}
    where
    antisym : Antisymmetric (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ <₁ ≤₂)
    antisym (inj₁ x₁<y₁) (inj₁ y₁<x₁) =
      ⊥-elim {_ × _} $ asym₁ x₁<y₁ y₁<x₁
    antisym (inj₁ x₁<y₁) (inj₂ y≈≤x)  =
      ⊥-elim {_ × _} $ irrefl₁ (sym₁ $ proj₁ y≈≤x) x₁<y₁
    antisym (inj₂ x≈≤y)  (inj₁ y₁<x₁) =
      ⊥-elim {_ × _} $ irrefl₁ (sym₁ $ proj₁ x≈≤y) y₁<x₁
    antisym (inj₂ x≈≤y)  (inj₂ y≈≤x)  =
      proj₁ x≈≤y , antisym₂ (proj₂ x≈≤y) (proj₂ y≈≤x)

  ×-lex-≤-antisymmetric
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁}
    -> PartialOrder ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂}
    -> Antisymmetric ≈₂ ≤₂
    -> Antisymmetric (≈₁ ×-Rel ≈₂) (×-Lex-≤ ≈₁ ≤₁ ≤₂)
  ×-lex-≤-antisymmetric {≈₁ = ≈₁} {≤₁ = ≤₁} po₁ {≤₂ = ≤₂} antisym₂
                        {x} {y} =
    ×-lex-antisymmetric {<₁ = ≤⟶< ≈₁ ≤₁} sym₁ irrefl₁ asym₁
                        {≤₂ = ≤₂} antisym₂ {x} {y}
    where
    open module PO = PartialOrder po₁
    refl₁   : Reflexive _≡_ ≈₁
    refl₁   = Preorder.refl (Equivalence.preorder equiv)
    sym₁    : Symmetric ≈₁
    sym₁    = Equivalence.sym equiv
    irrefl₁ : Irreflexive ≈₁ (≤⟶< ≈₁ ≤₁)
    irrefl₁ = irrefl-≤⟶< ≈₁ ≤₁
    asym₁   : Asymmetric (≤⟶< ≈₁ ≤₁)
    asym₁   = trans∧irr⟶asym refl₁ (trans-≤⟶< po₁) irrefl₁

  ×-asymmetric₁
    :  forall {a₁} -> {<₁ : Rel a₁}
    -> Asymmetric <₁
    -> forall {a₂} -> {∼₂ : Rel a₂}
    -> Asymmetric (<₁ ×-Rel ∼₂)
  ×-asymmetric₁ asym₁ = \x<y y<x -> asym₁ (proj₁ x<y) (proj₁ y<x)

  ×-asymmetric₂
    :  forall {a₁} -> {∼₁ : Rel a₁}
    -> forall {a₂} -> {<₂ : Rel a₂}
    -> Asymmetric <₂
    -> Asymmetric (∼₁ ×-Rel <₂)
  ×-asymmetric₂ asym₂ = \x<y y<x -> asym₂ (proj₂ x<y) (proj₂ y<x)

  ×-lex-asymmetric
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁}
    -> Symmetric ≈₁ -> ≈₁ Respects₂ <₁ -> Asymmetric <₁
    -> forall {a₂} -> {<₂ : Rel a₂}
    -> Asymmetric <₂
    -> Asymmetric (×-Lex ≈₁ <₁ <₂)
  ×-lex-asymmetric {≈₁ = ≈₁} {<₁ = <₁} sym₁ resp₁ asym₁
                             {<₂ = <₂} asym₂ {x} {y} = asym {x} {y}
    where
    irrefl₁ : Irreflexive ≈₁ <₁
    irrefl₁ = asym⟶irr resp₁ sym₁ asym₁

    asym : Asymmetric (×-Lex ≈₁ <₁ <₂)
    asym (inj₁ x₁<y₁) (inj₁ y₁<x₁) = asym₁ x₁<y₁ y₁<x₁
    asym (inj₁ x₁<y₁) (inj₂ y≈<x)  = irrefl₁ (sym₁ $ proj₁ y≈<x) x₁<y₁
    asym (inj₂ x≈<y)  (inj₁ y₁<x₁) = irrefl₁ (sym₁ $ proj₁ x≈<y) y₁<x₁
    asym (inj₂ x≈<y)  (inj₂ y≈<x)  = asym₂ (proj₂ x≈<y) (proj₂ y≈<x)

  _×-≈-respects₂_
    :  forall {a₁} -> {≈₁ ∼₁ : Rel a₁}
    -> ≈₁ Respects₂ ∼₁
    -> forall {a₂} -> {≈₂ ∼₂ : Rel a₂}
    -> ≈₂ Respects₂ ∼₂
    -> (≈₁ ×-Rel ≈₂) Respects₂ (∼₁ ×-Rel ∼₂)
  _×-≈-respects₂_ {≈₁ = ≈₁} {∼₁ = ∼₁} resp₁
                  {≈₂ = ≈₂} {∼₂ = ∼₂} resp₂ =
    (\{x y z} -> resp¹ {x} {y} {z}) ,
    (\{x y z} -> resp² {x} {y} {z})
    where
    ∼ = ∼₁ ×-Rel ∼₂

    resp¹ : forall {x} -> (≈₁ ×-Rel ≈₂) Respects (∼ x)
    resp¹ y≈y' x∼y = proj₁ resp₁ (proj₁ y≈y') (proj₁ x∼y) ,
                     proj₁ resp₂ (proj₂ y≈y') (proj₂ x∼y)

    resp² : forall {y} -> (≈₁ ×-Rel ≈₂) Respects (flip₁ ∼ y)
    resp² x≈x' x∼y = proj₂ resp₁ (proj₁ x≈x') (proj₁ x∼y) ,
                     proj₂ resp₂ (proj₂ x≈x') (proj₂ x∼y)

  ×-lex-≈-respects₂
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁}
    -> Equivalence ≈₁ -> ≈₁ Respects₂ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂}
    -> ≈₂ Respects₂ <₂
    -> (≈₁ ×-Rel ≈₂) Respects₂ (×-Lex ≈₁ <₁ <₂)
  ×-lex-≈-respects₂ {≈₁ = ≈₁} {<₁ = <₁} eq₁ resp₁
                    {≈₂ = ≈₂} {<₂ = <₂}     resp₂ =
    (\{x y z} -> resp¹ {x} {y} {z}) ,
    (\{x y z} -> resp² {x} {y} {z})
    where
    < = ×-Lex ≈₁ <₁ <₂

    trans₁ : Transitive ≈₁
    trans₁ = Preorder.trans (Equivalence.preorder eq₁)
    sym₁   : Symmetric ≈₁
    sym₁   = Equivalence.sym eq₁

    resp¹ : forall {x} -> (≈₁ ×-Rel ≈₂) Respects (< x)
    resp¹ y≈y' (inj₁ x₁<y₁) = inj₁ (proj₁ resp₁ (proj₁ y≈y') x₁<y₁)
    resp¹ y≈y' (inj₂ x≈<y)  =
      inj₂ ( trans₁ (proj₁ x≈<y) (proj₁ y≈y')
           , proj₁ resp₂ (proj₂ y≈y') (proj₂ x≈<y) )

    resp² : forall {y} -> (≈₁ ×-Rel ≈₂) Respects (flip₁ < y)
    resp² x≈x' (inj₁ x₁<y₁) = inj₁ (proj₂ resp₁ (proj₁ x≈x') x₁<y₁)
    resp² x≈x' (inj₂ x≈<y)  =
      inj₂ ( trans₁ (sym₁ $ proj₁ x≈x') (proj₁ x≈<y)
           , proj₂ resp₂ (proj₂ x≈x') (proj₂ x≈<y) )

  ×-lex-≤-≈-respects₂
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁}
    -> Equivalence ≈₁ -> ≈₁ Respects₂ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂}
    -> ≈₂ Respects₂ ≤₂
    -> (≈₁ ×-Rel ≈₂) Respects₂ (×-Lex-≤ ≈₁ ≤₁ ≤₂)
  ×-lex-≤-≈-respects₂ eq₁ resp₁ resp₂ =
    ×-lex-≈-respects₂ eq₁ (resp-≤⟶< eq₁ resp₁) resp₂

  _×-decidable_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Decidable ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Decidable ∼₂
    -> Decidable (∼₁ ×-Rel ∼₂)
  _×-decidable_ dec₁ dec₂ = \x y ->
    dec₁ (proj₁ x) (proj₁ y)
      ×-dec
    dec₂ (proj₂ x) (proj₂ y)

  ×-lex-decidable
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁}
    -> Decidable ≈₁ -> Decidable <₁
    -> forall {a₂} -> {≤₂ : Rel a₂}
    -> Decidable ≤₂
    -> Decidable (×-Lex ≈₁ <₁ ≤₂)
  ×-lex-decidable dec-≈₁ dec-<₁ dec-≤₂ = \x y ->
    dec-<₁ (proj₁ x) (proj₁ y)
      ⊎-dec
    (dec-≈₁ (proj₁ x) (proj₁ y)
       ×-dec
     dec-≤₂ (proj₂ x) (proj₂ y))

  ×-lex-≤-decidable
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁}
    -> Decidable ≈₁ -> Decidable ≤₁
    -> forall {a₂} -> {≤₂ : Rel a₂}
    -> Decidable ≤₂
    -> Decidable (×-Lex-≤ ≈₁ ≤₁ ≤₂)
  ×-lex-≤-decidable dec-≈₁ dec-≤₁ dec-≤₂ =
    ×-lex-decidable dec-≈₁ (decidable-≤⟶< dec-≈₁ dec-≤₁) dec-≤₂

  ×-total₁
    :  forall {a₁} -> {∼₁ : Rel a₁}
    -> Symmetric ∼₁ -> Total ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂}
    -> Total ∼₂
    -> Total (∼₁ ×-Rel ∼₂)
  ×-total₁ {∼₁ = ∼₁} sym₁ total₁ {∼₂ = ∼₂} total₂ = total
    where
    total : Total (∼₁ ×-Rel ∼₂)
    total x y with total₁ (proj₁ x) (proj₁ y)
                 | total₂ (proj₂ x) (proj₂ y)
    total x y | inj₁ x₁∼y₁ | inj₁ x₂∼y₂ = inj₁ (     x₁∼y₁ , x₂∼y₂)
    total x y | inj₁ x₁∼y₁ | inj₂ y₂∼x₂ = inj₂ (sym₁ x₁∼y₁ , y₂∼x₂)
    total x y | inj₂ y₁∼x₁ | inj₂ y₂∼x₂ = inj₂ (     y₁∼x₁ , y₂∼x₂)
    total x y | inj₂ y₁∼x₁ | inj₁ x₂∼y₂ = inj₁ (sym₁ y₁∼x₁ , x₂∼y₂)

  ×-total₂
    :  forall {a₁} -> {∼₁ : Rel a₁}
    -> Total ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂}
    -> Symmetric ∼₂ -> Total ∼₂
    -> Total (∼₁ ×-Rel ∼₂)
  ×-total₂ {∼₁ = ∼₁} total₁ {∼₂ = ∼₂} sym₂ total₂ x y =
    map-⊎ swap swap $ total (swap x) (swap y)
    where
    total : Total (∼₂ ×-Rel ∼₁)
    total = ×-total₁ sym₂ total₂ total₁

  ×-lex-total
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁} -> Total <₁
    -> forall {a₂} -> {   ≤₂ : Rel a₂}
    -> Total (×-Lex ≈₁ <₁ ≤₂)
  ×-lex-total {≈₁ = ≈₁} {<₁ = <₁} total₁ {≤₂ = ≤₂} = total
    where
    total : Total (×-Lex ≈₁ <₁ ≤₂)
    total x y with total₁ (proj₁ x) (proj₁ y)
    total x y | inj₁ x₁<y₁ = inj₁ (inj₁ x₁<y₁)
    total x y | inj₂ x₁>y₁ = inj₂ (inj₁ x₁>y₁)

  ×-lex-≤-total
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁}
    -> Symmetric ≈₁ -> Decidable ≈₁
    -> Antisymmetric ≈₁ ≤₁ -> Total ≤₁
    -> forall {a₂} -> {≤₂ : Rel a₂}
    -> Total ≤₂
    -> Total (×-Lex-≤ ≈₁ ≤₁ ≤₂)
  ×-lex-≤-total {≈₁ = ≈₁} {≤₁ = ≤₁} sym₁ dec₁ antisym₁ total₁
                          {≤₂ = ≤₂} total₂ = total
    where
    tri₁ : Trichotomous ≈₁ (≤⟶< ≈₁ ≤₁)
    tri₁ = total-≤⟶tri-< sym₁ dec₁ antisym₁ total₁

    total : Total (×-Lex-≤ ≈₁ ≤₁ ≤₂)
    total x y with tri₁ (proj₁ x) (proj₁ y)
    total x y | Tri₁ x₁<y₁ x₁≉y₁ x₁≯y₁ = inj₁ (inj₁ x₁<y₁)
    total x y | Tri₃ x₁≮y₁ x₁≉y₁ x₁>y₁ = inj₂ (inj₁ x₁>y₁)
    total x y | Tri₂ x₁≮y₁ x₁≈y₁ x₁≯y₁ with total₂ (proj₂ x) (proj₂ y)
    total x y | Tri₂ x₁≮y₁ x₁≈y₁ x₁≯y₁ | inj₁ x₂≤y₂ =
      inj₁ (inj₂ (x₁≈y₁ , x₂≤y₂))
    total x y | Tri₂ x₁≮y₁ x₁≈y₁ x₁≯y₁ | inj₂ x₂≥y₂ =
      inj₂ (inj₂ (sym₁ x₁≈y₁ , x₂≥y₂))

------------------------------------------------------------------------
-- Some collections of properties are also preserved

abstract

  _×-preorder_
    :  forall {a₁} -> {≈₁ ∼₁ : Rel a₁} -> Preorder ≈₁ ∼₁
    -> forall {a₂} -> {≈₂ ∼₂ : Rel a₂} -> Preorder ≈₂ ∼₂
    -> Preorder (≈₁ ×-Rel ≈₂) (∼₁ ×-Rel ∼₂)
  _×-preorder_ {∼₁ = ∼₁} pre₁ {∼₂ = ∼₂} pre₂ = record
    { refl  = \{x y} ->
              _×-reflexive_  {∼₁ = ∼₁} (refl  pre₁)
                             {∼₂ = ∼₂} (refl  pre₂) {x} {y}
    ; trans = \{x y z} ->
              _×-transitive_ {∼₁ = ∼₁} (trans pre₁)
                             {∼₂ = ∼₂} (trans pre₂) {x} {y} {z}
    }
    where open Preorder

  _×-preorder-≡_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Preorder _≡_ ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Preorder _≡_ ∼₂
    -> Preorder _≡_ (∼₁ ×-Rel ∼₂)
  _×-preorder-≡_ {∼₁ = ∼₁} pre₁ {∼₂ = ∼₂} pre₂ = record
    { refl  = _×-reflexive-≡_ {∼₁ = ∼₁} (refl  pre₁)
                              {∼₂ = ∼₂} (refl  pre₂)
    ; trans = \{x y z} ->
              _×-transitive_  {∼₁ = ∼₁} (trans pre₁)
                              {∼₂ = ∼₂} (trans pre₂) {x} {y} {z}
    }
    where open Preorder

  _×-equivalence_
    :  forall {a₁} -> {≈₁ : Rel a₁} -> Equivalence ≈₁
    -> forall {a₂} -> {≈₂ : Rel a₂} -> Equivalence ≈₂
    -> Equivalence (≈₁ ×-Rel ≈₂)
  _×-equivalence_ {≈₁ = ≈₁} eq₁ {≈₂ = ≈₂} eq₂ = record
    { preorder = preorder eq₁ ×-preorder-≡ preorder eq₂
    ; sym      = \{x y} ->
                 _×-symmetric_ {∼₁ = ≈₁} (sym eq₁)
                               {∼₂ = ≈₂} (sym eq₂) {x} {y}
    }
    where open Equivalence

  _×-partialOrder_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> PartialOrder ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> PartialOrder ≈₂ ≤₂
    -> PartialOrder (≈₁ ×-Rel ≈₂) (≤₁ ×-Rel ≤₂)
  _×-partialOrder_ {≤₁ = ≤₁} po₁ {≤₂ = ≤₂} po₂ = record
    { equiv    = equiv    po₁ ×-equivalence equiv    po₂
    ; preorder = preorder po₁ ×-preorder    preorder po₂
    ; antisym  = \{x y} ->
                 _×-antisymmetric_ {≤₁ = ≤₁} (antisym po₁)
                                   {≤₂ = ≤₂} (antisym po₂) {x} {y}
    ; ≈-resp-≤ = ≈-resp-≤ po₁ ×-≈-respects₂ ≈-resp-≤ po₂
    }
    where open PartialOrder

  ×-lex-partialOrder
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> PartialOrder ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> PartialOrder ≈₂ ≤₂
    -> PartialOrder (≈₁ ×-Rel ≈₂) (×-Lex-≤ ≈₁ ≤₁ ≤₂)
  ×-lex-partialOrder {≈₁ = ≈₁} {≤₁ = ≤₁} po₁ {≤₂ = ≤₂} po₂ = record
    { equiv    = equiv po₁ ×-equivalence equiv po₂
    ; preorder = record
        { refl  = \{x y} ->
                  ×-lex-≤-reflexive ≈₁ ≤₁ ≤₂ (refl $ preorder po₂)
                  {x} {y}
        ; trans = \{x y z} ->
                  ×-lex-≤-transitive           po₁
                                     {≤₂ = ≤₂} (trans (preorder po₂))
                  {x} {y} {z}
        }
    ; antisym  = \{x y} ->
                 ×-lex-≤-antisymmetric {≤₁ = ≤₁} po₁
                                       {≤₂ = ≤₂} (antisym po₂) {x} {y}
    ; ≈-resp-≤ = ×-lex-≤-≈-respects₂ (equiv po₁) (≈-resp-≤ po₁)
                                                 (≈-resp-≤ po₂)
    }
    where
    open PartialOrder
    open Preorder

  _×-strictPartialOrder_
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁} -> StrictPartialOrder ≈₁ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂} -> StrictPartialOrder ≈₂ <₂
    -> StrictPartialOrder (≈₁ ×-Rel ≈₂) (<₁ ×-Rel <₂)
  _×-strictPartialOrder_ {<₁ = <₁} spo₁ {≈₂ = ≈₂} {<₂ = <₂} spo₂ =
    record
      { equiv    = equiv spo₁ ×-equivalence equiv spo₂
      ; irrefl   = \{x y} ->
                   ×-irreflexive₁           {<₁ = <₁} (irrefl spo₁)
                                  {≈₂ = ≈₂} {<₂ = <₂} {x} {y}
      ; trans    = \{x y z} ->
                   _×-transitive_ {∼₁ = <₁} (trans spo₁)
                                  {∼₂ = <₂} (trans spo₂) {x} {y} {z}
      ; ≈-resp-< = ≈-resp-< spo₁ ×-≈-respects₂ ≈-resp-< spo₂
      }
    where open StrictPartialOrder

  _×-lex-strictPartialOrder_
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁}
    -> StrictPartialOrder ≈₁ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂}
    -> StrictPartialOrder ≈₂ <₂
    -> StrictPartialOrder (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ <₁ <₂)
  _×-lex-strictPartialOrder_ {<₁ = <₁} spo₁ {<₂ = <₂} spo₂ =
    record
      { equiv    = equiv spo₁ ×-equivalence equiv spo₂
      ; irrefl   = \{x y} ->
                   _×-lex-irreflexive_ <₁ (irrefl spo₁)
                                       <₂ (irrefl spo₂) {x} {y}
      ; trans    = \{x y z} ->
                   ×-lex-transitive
                     {<₁ = <₁} (equiv spo₁) (≈-resp-< spo₁) (trans spo₁)
                     {≤₂ = <₂} (trans spo₂) {x} {y} {z}
      ; ≈-resp-< = ×-lex-≈-respects₂ (equiv spo₁) (≈-resp-< spo₁)
                                                  (≈-resp-< spo₂)
      }
    where open StrictPartialOrder

------------------------------------------------------------------------
-- And the game can be taken even further...

_×-setoid_ : Setoid -> Setoid -> Setoid
s₁ ×-setoid s₂ = record
  { carrier = carrier s₁ ×             carrier s₂
  ; _≈_     = _≈_     s₁ ×-Rel         _≈_     s₂
  ; equiv   = equiv   s₁ ×-equivalence equiv   s₂
  }
  where open Setoid

_×-decSetoid_ : DecSetoid -> DecSetoid -> DecSetoid
ds₁ ×-decSetoid ds₂ = record
  { setoid = setoid ds₁ ×-setoid    setoid ds₂
  ; _≟_    = _≟_    ds₁ ×-decidable _≟_    ds₂
  }
  where open DecSetoid

_×-poset_ : Poset -> Poset -> Poset
po₁ ×-poset po₂ = record
  { carrier = carrier po₁ ×       carrier po₂
  ; _≈_     = _≈_     po₁ ×-Rel   _≈_     po₂
  ; _≤_     = ×-Lex-≤ (_≈_ po₁) (_≤_ po₁) (_≤_ po₂)
  ; ord     = ×-lex-partialOrder (ord po₁) (ord po₂)
  }
  where
  open Poset
  open PartialOrder

_×-decTotOrder_ : DecTotOrder -> DecTotOrder -> DecTotOrder
dto₁ ×-decTotOrder dto₂ = record
  { poset = poset dto₁ ×-poset     poset dto₂
  ; _≟_   = _≟_   dto₁ ×-decidable _≟_   dto₂
  ; _≤?_  = ×-lex-≤-decidable (_≟_ dto₁) (_≤?_ dto₁) (_≤?_ dto₂)
  ; total = ×-lex-≤-total (sym (equiv (ord (poset dto₁))))
                          (_≟_ dto₁)
                          (antisym (ord (poset dto₁)))
                          (total dto₁)
                          (total dto₂)
  }
  where
  open DecTotOrder
  open Poset
  open PartialOrder
  open Equivalence
