------------------------------------------------------------------------
-- Pointwise products of binary relations
------------------------------------------------------------------------

module Relation.Binary.Product.Pointwise where

open import Logic
open import Data.Function
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private
 module Dummy {a₁ a₂ : Set} where

  infixr 2 _×-Rel_

  -- Previously a function,
  --
  --   ∼₁ ×-Rel ∼₂ = (∼₁ on₁ proj₁) -×- (∼₂ on₁ proj₂),
  --
  -- was used instead of this data type. However, it is easier to
  -- infer the arguments of a data type than of a function, so now
  -- fewer arguments need to be given explicitly in the proofs below.

  data _×-Rel_ (_∼₁_ : Rel a₁) (_∼₂_ : Rel a₂) (x y : a₁ × a₂)
         : Set where
    _,-rel_ :  proj₁ x ∼₁ proj₁ y
            -> proj₂ x ∼₂ proj₂ y
            -> (_∼₁_ ×-Rel _∼₂_) x y

  ,-rel₁ :  forall {_∼₁_ _∼₂_ x y}
          -> (_∼₁_ ×-Rel _∼₂_) x y -> proj₁ x ∼₁ proj₁ y
  ,-rel₁ (r₁ ,-rel r₂) = r₁

  ,-rel₂ :  forall {_∼₁_ _∼₂_ x y}
          -> (_∼₁_ ×-Rel _∼₂_) x y -> proj₂ x ∼₂ proj₂ y
  ,-rel₂ (r₁ ,-rel r₂) = r₂

  -- Some properties which are preserved by ×-Rel (under certain
  -- assumptions).

  abstract

    _×-reflexive_
      :  forall {≈₁ ∼₁ ≈₂ ∼₂}
      -> Reflexive ≈₁ ∼₁ -> Reflexive ≈₂ ∼₂
      -> Reflexive (≈₁ ×-Rel ≈₂) (∼₁ ×-Rel ∼₂)
    refl₁ ×-reflexive refl₂ = \x≈y ->
      refl₁ (,-rel₁ x≈y) ,-rel refl₂ (,-rel₂ x≈y)

    _×-refl_
      : forall {∼₁ ∼₂} -> Refl ∼₁ -> Refl ∼₂ -> Refl (∼₁ ×-Rel ∼₂)
    refl₁ ×-refl refl₂ = refl₁ ,-rel refl₂

    ×-irreflexive₁
      :  forall {≈₁ <₁ ≈₂ <₂}
      -> Irreflexive ≈₁ <₁ -> Irreflexive (≈₁ ×-Rel ≈₂) (<₁ ×-Rel <₂)
    ×-irreflexive₁ ir = \x≈y x<y -> ir (,-rel₁ x≈y) (,-rel₁ x<y)

    ×-irreflexive₂
      :  forall {≈₁ <₁ ≈₂ <₂}
      -> Irreflexive ≈₂ <₂ -> Irreflexive (≈₁ ×-Rel ≈₂) (<₁ ×-Rel <₂)
    ×-irreflexive₂ ir = \x≈y x<y -> ir (,-rel₂ x≈y) (,-rel₂ x<y)

    _×-symmetric_
      :  forall {∼₁ ∼₂}
      -> Symmetric ∼₁ -> Symmetric ∼₂ -> Symmetric (∼₁ ×-Rel ∼₂)
    (sym₁ ×-symmetric sym₂) (x₁∼y₁ ,-rel x₂∼y₂) =
      sym₁ x₁∼y₁ ,-rel sym₂ x₂∼y₂

    _×-transitive_
      :  forall {∼₁ ∼₂}
      -> Transitive ∼₁ -> Transitive ∼₂
      -> Transitive (∼₁ ×-Rel ∼₂)
    (trans₁ ×-transitive trans₂)
      (x₁∼y₁ ,-rel x₂∼y₂) (y₁∼z₁ ,-rel y₂∼z₂) =
      trans₁ x₁∼y₁ y₁∼z₁ ,-rel trans₂ x₂∼y₂ y₂∼z₂

    _×-antisymmetric_
      :  forall {≈₁ ≤₁ ≈₂ ≤₂}
      -> Antisymmetric ≈₁ ≤₁ -> Antisymmetric ≈₂ ≤₂
      -> Antisymmetric (≈₁ ×-Rel ≈₂) (≤₁ ×-Rel ≤₂)
    antisym₁ ×-antisymmetric antisym₂ = \x≤y y≤x ->
      antisym₁ (,-rel₁ x≤y) (,-rel₁ y≤x)
        ,-rel
      antisym₂ (,-rel₂ x≤y) (,-rel₂ y≤x)

    ×-asymmetric₁
      :  forall {<₁ ∼₂}
      -> Asymmetric <₁ -> Asymmetric (<₁ ×-Rel ∼₂)
    ×-asymmetric₁ asym₁ = \x<y y<x -> asym₁ (,-rel₁ x<y) (,-rel₁ y<x)

    ×-asymmetric₂
      :  forall {∼₁ <₂}
      -> Asymmetric <₂ -> Asymmetric (∼₁ ×-Rel <₂)
    ×-asymmetric₂ asym₂ = \x<y y<x -> asym₂ (,-rel₂ x<y) (,-rel₂ y<x)

    _×-≈-respects₂_
      :  forall {≈₁ ∼₁ ≈₂ ∼₂}
      -> ≈₁ Respects₂ ∼₁ -> ≈₂ Respects₂ ∼₂
      -> (≈₁ ×-Rel ≈₂) Respects₂ (∼₁ ×-Rel ∼₂)
    _×-≈-respects₂_ {≈₁ = ≈₁} {∼₁ = ∼₁} {≈₂ = ≈₂} {∼₂ = ∼₂}
                    resp₁ resp₂ =
      (\{x y z} -> resp¹ {x} {y} {z}) ,
      (\{x y z} -> resp² {x} {y} {z})
      where
      ∼ = ∼₁ ×-Rel ∼₂

      resp¹ : forall {x} -> (≈₁ ×-Rel ≈₂) Respects (∼ x)
      resp¹ y≈y' x∼y = proj₁ resp₁ (,-rel₁ y≈y') (,-rel₁ x∼y) ,-rel
                       proj₁ resp₂ (,-rel₂ y≈y') (,-rel₂ x∼y)

      resp² : forall {y} -> (≈₁ ×-Rel ≈₂) Respects (flip₁ ∼ y)
      resp² x≈x' x∼y = proj₂ resp₁ (,-rel₁ x≈x') (,-rel₁ x∼y) ,-rel
                       proj₂ resp₂ (,-rel₂ x≈x') (,-rel₂ x∼y)

    ×-total
      :  forall {∼₁ ∼₂}
      -> Symmetric ∼₁ -> Total ∼₁ -> Total ∼₂ -> Total (∼₁ ×-Rel ∼₂)
    ×-total {∼₁ = ∼₁} {∼₂ = ∼₂} sym₁ total₁ total₂ = total
      where
      total : Total (∼₁ ×-Rel ∼₂)
      total x y with total₁ (proj₁ x) (proj₁ y)
                   | total₂ (proj₂ x) (proj₂ y)
      ... | inj₁ x₁∼y₁ | inj₁ x₂∼y₂ = inj₁ (     x₁∼y₁ ,-rel x₂∼y₂)
      ... | inj₁ x₁∼y₁ | inj₂ y₂∼x₂ = inj₂ (sym₁ x₁∼y₁ ,-rel y₂∼x₂)
      ... | inj₂ y₁∼x₁ | inj₂ y₂∼x₂ = inj₂ (     y₁∼x₁ ,-rel y₂∼x₂)
      ... | inj₂ y₁∼x₁ | inj₁ x₂∼y₂ = inj₁ (sym₁ y₁∼x₁ ,-rel x₂∼y₂)

    -- This definition could reuse Relation.Nullary.Product._×-dec_,
    -- but at the cost of _two_ extra conversion functions.

    _×-decidable_
      :  forall {∼₁ ∼₂}
      -> Decidable ∼₁ -> Decidable ∼₂ -> Decidable (∼₁ ×-Rel ∼₂)
    (dec₁ ×-decidable dec₂) (x₁ , x₂) (y₁ , y₂)
      with dec₁ x₁ y₁ | dec₂ x₂ y₂
    ... | yes p₁ | yes p₂ = yes (p₁ ,-rel p₂)
    ... | no  ¬p | _      = no (¬p ∘ ,-rel₁)
    ... | _      | no  ¬p = no (¬p ∘ ,-rel₂)

  -- Some collections of properties which are preserved by ×-Rel.

  abstract

    _×-isEquivalence_
      :  forall {≈₁ ≈₂}
      -> IsEquivalence ≈₁ -> IsEquivalence ≈₂
      -> IsEquivalence (≈₁ ×-Rel ≈₂)
    eq₁ ×-isEquivalence eq₂ = record
      { refl  = refl  eq₁ ×-refl        refl  eq₂
      ; sym   = sym   eq₁ ×-symmetric   sym   eq₂
      ; trans = trans eq₁ ×-transitive  trans eq₂
      }
      where open IsEquivalence

    _×-isPreorder_
      :  forall {≈₁ ∼₁ ≈₂ ∼₂}
      -> IsPreorder ≈₁ ∼₁ -> IsPreorder ≈₂ ∼₂
      -> IsPreorder (≈₁ ×-Rel ≈₂) (∼₁ ×-Rel ∼₂)
    pre₁ ×-isPreorder pre₂ = record
      { isEquivalence = isEquivalence pre₁ ×-isEquivalence
                        isEquivalence pre₂
      ; refl          = refl  pre₁    ×-reflexive   refl     pre₂
      ; trans         = trans pre₁    ×-transitive  trans    pre₂
      ; ≈-resp-∼      = ≈-resp-∼ pre₁ ×-≈-respects₂ ≈-resp-∼ pre₂
      }
      where open IsPreorder

    _×-isDecEquivalence_
      :  forall {≈₁ ≈₂}
      -> IsDecEquivalence ≈₁ -> IsDecEquivalence ≈₂
      -> IsDecEquivalence (≈₁ ×-Rel ≈₂)
    eq₁ ×-isDecEquivalence eq₂ = record
      { isEquivalence = isEquivalence eq₁ ×-isEquivalence
                        isEquivalence eq₂
      ; _≟_           = _≟_ eq₁ ×-decidable _≟_ eq₂
      }
      where open IsDecEquivalence

    _×-isPartialOrder_
      :  forall {≈₁ ≤₁ ≈₂ ≤₂}
      -> IsPartialOrder ≈₁ ≤₁ -> IsPartialOrder ≈₂ ≤₂
      -> IsPartialOrder (≈₁ ×-Rel ≈₂) (≤₁ ×-Rel ≤₂)
    po₁ ×-isPartialOrder po₂ = record
      { isPreorder = isPreorder po₁ ×-isPreorder    isPreorder po₂
      ; antisym    = antisym    po₁ ×-antisymmetric antisym    po₂
      }
      where open IsPartialOrder

    _×-isStrictPartialOrder_
      :  forall {≈₁ <₁ ≈₂ <₂}
      -> IsStrictPartialOrder ≈₁ <₁ -> IsStrictPartialOrder ≈₂ <₂
      -> IsStrictPartialOrder (≈₁ ×-Rel ≈₂) (<₁ ×-Rel <₂)
    spo₁ ×-isStrictPartialOrder spo₂ =
      record
        { isEquivalence = isEquivalence spo₁ ×-isEquivalence
                          isEquivalence spo₂
        ; irrefl        = ×-irreflexive₁ (irrefl spo₁)
        ; trans         = trans spo₁ ×-transitive trans spo₂
        ; ≈-resp-<      = ≈-resp-< spo₁ ×-≈-respects₂ ≈-resp-< spo₂
        }
      where open IsStrictPartialOrder

open Dummy public

-- "Packages" (e.g. setoids) can also be combined.

_×-preorder_ : Preorder -> Preorder -> Preorder
p₁ ×-preorder p₂ = record
  { carrier    = carrier    p₁ ×            carrier    p₂
  ; _≈_        = _≈_        p₁ ×-Rel        _≈_        p₂
  ; _∼_        = _∼_        p₁ ×-Rel        _∼_        p₂
  ; isPreorder = isPreorder p₁ ×-isPreorder isPreorder p₂
  }
  where open Preorder

_×-setoid_ : Setoid -> Setoid -> Setoid
s₁ ×-setoid s₂ = record
  { carrier       = carrier       s₁ ×               carrier       s₂
  ; _≈_           = _≈_           s₁ ×-Rel           _≈_           s₂
  ; isEquivalence = isEquivalence s₁ ×-isEquivalence isEquivalence s₂
  }
  where open Setoid

_×-decSetoid_ : DecSetoid -> DecSetoid -> DecSetoid
s₁ ×-decSetoid s₂ = record
  { carrier          = carrier s₁ ×     carrier s₂
  ; _≈_              = _≈_     s₁ ×-Rel _≈_     s₂
  ; isDecEquivalence = isDecEquivalence s₁ ×-isDecEquivalence
                       isDecEquivalence s₂
  }
  where open DecSetoid

_×-poset_ : Poset -> Poset -> Poset
s₁ ×-poset s₂ = record
  { carrier        = carrier s₁ ×     carrier s₂
  ; _≈_            = _≈_     s₁ ×-Rel _≈_     s₂
  ; _≤_            = _≤_     s₁ ×-Rel _≤_     s₂
  ; isPartialOrder = isPartialOrder s₁ ×-isPartialOrder
                     isPartialOrder s₂
  }
  where open Poset

_×-strictPartialOrder_
  : StrictPartialOrder -> StrictPartialOrder -> StrictPartialOrder
s₁ ×-strictPartialOrder s₂ = record
  { carrier              = carrier s₁ ×     carrier s₂
  ; _≈_                  = _≈_     s₁ ×-Rel _≈_     s₂
  ; _<_                  = _<_     s₁ ×-Rel _<_     s₂
  ; isStrictPartialOrder = isStrictPartialOrder s₁
                             ×-isStrictPartialOrder
                           isStrictPartialOrder s₂
  }
  where open StrictPartialOrder
