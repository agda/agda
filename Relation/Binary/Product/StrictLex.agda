------------------------------------------------------------------------
-- Lexicographic products of binary relations
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a strict partial order.

module Relation.Binary.Product.StrictLex where

open import Logic
open import Data.Function
open import Data.Product
open import Data.Sum
open import Relation.Nullary.Product
open import Relation.Nullary.Sum
open import Relation.Binary
open import Relation.Binary.Consequences
import Relation.Binary.Product.Pointwise as Pointwise
open Pointwise using (_×-Rel_)

private
 module Dummy {a₁ a₂ : Set} where

  ×-Lex : (≈₁ <₁ : Rel a₁) -> (≤₂ : Rel a₂) -> Rel (a₁ × a₂)
  ×-Lex ≈₁ <₁ ≤₂ = (<₁ on₁ proj₁) -⊎- (≈₁ on₁ proj₁) -×- (≤₂ on₁ proj₂)

  -- Some properties which are preserved by ×-Lex (under certain
  -- assumptions).

  ×-reflexive
    :  forall ≈₁ ∼₁ {≈₂} ≤₂
    -> ≈₂ ⇒ ≤₂ -> (≈₁ ×-Rel ≈₂) ⇒ (×-Lex ≈₁ ∼₁ ≤₂)
  ×-reflexive _ _ _ refl₂ = \x≈y ->
    inj₂ (proj₁ x≈y , refl₂ (proj₂ x≈y))

  _×-irreflexive_
    :  forall {≈₁ <₁} -> Irreflexive ≈₁ <₁
    -> forall {≈₂ <₂} -> Irreflexive ≈₂ <₂
    -> Irreflexive (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ <₁ <₂)
  (ir₁ ×-irreflexive ir₂) x≈y (inj₁ x₁<y₁) = ir₁ (proj₁ x≈y) x₁<y₁
  (ir₁ ×-irreflexive ir₂) x≈y (inj₂ x≈<y)  =
    ir₂ (proj₂ x≈y) (proj₂ x≈<y)

  ×-transitive
    :  forall {≈₁ <₁}
    -> IsEquivalence ≈₁ -> ≈₁ Respects₂ <₁ -> Transitive <₁
    -> forall {≤₂} -> Transitive ≤₂
    -> Transitive (×-Lex ≈₁ <₁ ≤₂)
  ×-transitive {≈₁ = ≈₁} {<₁ = <₁} eq₁ resp₁ trans₁
               {≤₂ = ≤₂} trans₂ {x} {y} {z} = trans {x} {y} {z}
    where
    module Eq₁ = IsEquivalence eq₁

    trans : Transitive (×-Lex ≈₁ <₁ ≤₂)
    trans (inj₁ x₁<y₁) (inj₁ y₁<z₁) = inj₁ (trans₁ x₁<y₁ y₁<z₁)
    trans (inj₁ x₁<y₁) (inj₂ y≈≤z)  =
      inj₁ (proj₁ resp₁ (proj₁ y≈≤z) x₁<y₁)
    trans (inj₂ x≈≤y)  (inj₁ y₁<z₁) =
      inj₁ (proj₂ resp₁ (Eq₁.sym $ proj₁ x≈≤y) y₁<z₁)
    trans (inj₂ x≈≤y)  (inj₂ y≈≤z)  =
      inj₂ ( Eq₁.trans (proj₁ x≈≤y) (proj₁ y≈≤z)
           , trans₂    (proj₂ x≈≤y) (proj₂ y≈≤z) )

  ×-antisymmetric
    :  forall {≈₁ <₁}
    -> Symmetric ≈₁ -> Irreflexive ≈₁ <₁ -> Asymmetric <₁
    -> forall {≈₂ ≤₂} -> Antisymmetric ≈₂ ≤₂
    -> Antisymmetric (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ <₁ ≤₂)
  ×-antisymmetric {≈₁ = ≈₁} {<₁ = <₁} sym₁ irrefl₁ asym₁
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

  ×-asymmetric
    :  forall {≈₁ <₁}
    -> Symmetric ≈₁ -> ≈₁ Respects₂ <₁ -> Asymmetric <₁
    -> forall {<₂} -> Asymmetric <₂
    -> Asymmetric (×-Lex ≈₁ <₁ <₂)
  ×-asymmetric {≈₁ = ≈₁} {<₁ = <₁} sym₁ resp₁ asym₁
               {<₂ = <₂} asym₂ {x} {y} = asym {x} {y}
    where
    irrefl₁ : Irreflexive ≈₁ <₁
    irrefl₁ = asym⟶irr resp₁ sym₁ asym₁

    asym : Asymmetric (×-Lex ≈₁ <₁ <₂)
    asym (inj₁ x₁<y₁) (inj₁ y₁<x₁) = asym₁ x₁<y₁ y₁<x₁
    asym (inj₁ x₁<y₁) (inj₂ y≈<x)  = irrefl₁ (sym₁ $ proj₁ y≈<x) x₁<y₁
    asym (inj₂ x≈<y)  (inj₁ y₁<x₁) = irrefl₁ (sym₁ $ proj₁ x≈<y) y₁<x₁
    asym (inj₂ x≈<y)  (inj₂ y≈<x)  = asym₂ (proj₂ x≈<y) (proj₂ y≈<x)

  ×-≈-respects₂
    :  forall {≈₁ <₁} -> IsEquivalence ≈₁ -> ≈₁ Respects₂ <₁
    -> forall {≈₂ <₂} -> ≈₂ Respects₂ <₂
    -> (≈₁ ×-Rel ≈₂) Respects₂ (×-Lex ≈₁ <₁ <₂)
  ×-≈-respects₂ {≈₁ = ≈₁} {<₁ = <₁} eq₁ resp₁
                {≈₂ = ≈₂} {<₂ = <₂}     resp₂ =
    (\{x y z} -> resp¹ {x} {y} {z}) ,
    (\{x y z} -> resp² {x} {y} {z})
    where
    < = ×-Lex ≈₁ <₁ <₂

    open IsEquivalence eq₁ renaming (sym to sym₁; trans to trans₁)

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

  ×-decidable
    :  forall {≈₁ <₁} -> Decidable ≈₁ -> Decidable <₁
    -> forall {≤₂} -> Decidable ≤₂
    -> Decidable (×-Lex ≈₁ <₁ ≤₂)
  ×-decidable dec-≈₁ dec-<₁ dec-≤₂ = \x y ->
    dec-<₁ (proj₁ x) (proj₁ y)
      ⊎-dec
    (dec-≈₁ (proj₁ x) (proj₁ y)
       ×-dec
     dec-≤₂ (proj₂ x) (proj₂ y))

  ×-total
    :  forall {≈₁ <₁} -> Total <₁
    -> forall {≤₂}
    -> Total (×-Lex ≈₁ <₁ ≤₂)
  ×-total {≈₁ = ≈₁} {<₁ = <₁} total₁ {≤₂ = ≤₂} = total
    where
    total : Total (×-Lex ≈₁ <₁ ≤₂)
    total x y with total₁ (proj₁ x) (proj₁ y)
    ... | inj₁ x₁<y₁ = inj₁ (inj₁ x₁<y₁)
    ... | inj₂ x₁>y₁ = inj₂ (inj₁ x₁>y₁)

  -- Some collections of properties which are preserved by ×-Lex.

  _×-isPreorder_
    :  forall {≈₁ ∼₁} -> IsPreorder ≈₁ ∼₁
    -> forall {≈₂ ∼₂} -> IsPreorder ≈₂ ∼₂
    -> IsPreorder (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ ∼₁ ∼₂)
  _×-isPreorder_ {≈₁ = ≈₁} {∼₁ = ∼₁} pre₁ {∼₂ = ∼₂} pre₂ = record
    { isEquivalence = Pointwise._×-isEquivalence_
                        (isEquivalence pre₁) (isEquivalence pre₂)
    ; reflexive     = \{x y} ->
                      ×-reflexive ≈₁ ∼₁ ∼₂ (reflexive pre₂) {x} {y}
    ; trans         = \{x y z} ->
                      ×-transitive
                        (isEquivalence pre₁) (≈-resp-∼ pre₁) (trans pre₁)
                        {≤₂ = ∼₂} (trans pre₂) {x} {y} {z}
    ; ≈-resp-∼      = ×-≈-respects₂ (isEquivalence pre₁)
                                        (≈-resp-∼ pre₁)
                                        (≈-resp-∼ pre₂)
    }
    where open IsPreorder

  _×-isStrictPartialOrder_
    :  forall {≈₁ <₁} -> IsStrictPartialOrder ≈₁ <₁
    -> forall {≈₂ <₂} -> IsStrictPartialOrder ≈₂ <₂
    -> IsStrictPartialOrder (≈₁ ×-Rel ≈₂) (×-Lex ≈₁ <₁ <₂)
  _×-isStrictPartialOrder_ {<₁ = <₁} spo₁ {<₂ = <₂} spo₂ =
    record
      { isEquivalence = Pointwise._×-isEquivalence_
                          (isEquivalence spo₁) (isEquivalence spo₂)
      ; irrefl        = \{x y} ->
                        _×-irreflexive_ {<₁ = <₁} (irrefl spo₁)
                                        {<₂ = <₂} (irrefl spo₂) {x} {y}
      ; trans         = \{x y z} ->
                        ×-transitive
                          {<₁ = <₁} (isEquivalence spo₁) (≈-resp-< spo₁)
                                    (trans spo₁)
                          {≤₂ = <₂} (trans spo₂) {x} {y} {z}
      ; ≈-resp-<      = ×-≈-respects₂ (isEquivalence spo₁)
                                          (≈-resp-< spo₁)
                                          (≈-resp-< spo₂)
      }
    where open IsStrictPartialOrder

open Dummy public

-- "Packages" (e.g. preorders) can also be combined.

_×-preorder_ : Preorder -> Preorder -> Preorder
p₁ ×-preorder p₂ = record
  { carrier    = carrier p₁ ×     carrier p₂
  ; _≈_        = _≈_     p₁ ×-Rel _≈_     p₂
  ; _∼_        = ×-Lex (_≈_ p₁) (_∼_ p₁) (_∼_ p₂)
  ; isPreorder = isPreorder p₁ ×-isPreorder isPreorder p₂
  }
  where open Preorder

_×-strictPartialOrder_
  : StrictPartialOrder -> StrictPartialOrder -> StrictPartialOrder
s₁ ×-strictPartialOrder s₂ = record
  { carrier              = carrier s₁ ×     carrier s₂
  ; _≈_                  = _≈_     s₁ ×-Rel _≈_     s₂
  ; _<_                  = ×-Lex (_≈_ s₁) (_<_ s₁) (_<_ s₂)
  ; isStrictPartialOrder = isStrictPartialOrder s₁
                             ×-isStrictPartialOrder
                           isStrictPartialOrder s₂
  }
  where open StrictPartialOrder
