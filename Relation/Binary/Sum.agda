------------------------------------------------------------------------
-- Sums of binary relations
------------------------------------------------------------------------

module Relation.Binary.Sum where

open import Logic
open import Data.Function
open import Data.Sum
open import Data.Product
open import Relation.Binary
open Π

infixr 1 _⊎-Rel_ _⊎-≤_

------------------------------------------------------------------------
-- Sums of relations

-- Pointwise sum.

data _⊎-Rel_ {a₁ : Set} (_∼₁_ : Rel a₁)
             {a₂ : Set} (_∼₂_ : Rel a₂)
             : Rel (a₁ ⊎ a₂) where
  inj₁-Rel :  forall {x y} -> x ∼₁ y
           -> _⊎-Rel_ _∼₁_ _∼₂_ (inj₁ x) (inj₁ y)
  inj₂-Rel :  forall {x y} -> x ∼₂ y
           -> _⊎-Rel_ _∼₁_ _∼₂_ (inj₂ x) (inj₂ y)

-- All left things are ≤ all right things.

data _⊎-≤_ {a₁ : Set} (_≤₁_ : Rel a₁)
           {a₂ : Set} (_≤₂_ : Rel a₂)
         : a₁ ⊎ a₂ -> a₁ ⊎ a₂ -> Set where
  ₁≤₂ : forall {x y}           -> _⊎-≤_ _≤₁_ _≤₂_ (inj₁ x) (inj₂ y)
  ₁≤₁ : forall {x y} -> x ≤₁ y -> _⊎-≤_ _≤₁_ _≤₂_ (inj₁ x) (inj₁ y)
  ₂≤₂ : forall {x y} -> x ≤₂ y -> _⊎-≤_ _≤₁_ _≤₂_ (inj₂ x) (inj₂ y)

------------------------------------------------------------------------
-- Helpers

abstract
 private

  ₂≁₁ :  forall {a₁} -> {∼₁ : Rel a₁}
      -> forall {a₂} -> {∼₂ : Rel a₂}
      -> forall {x y} -> ¬ (inj₂ x ⟨ ∼₁ ⊎-Rel ∼₂ ⟩₁ inj₁ y)
  ₂≁₁ ()

  ₁≁₂ :  forall {a₁} -> {∼₁ : Rel a₁}
      -> forall {a₂} -> {∼₂ : Rel a₂}
      -> forall {x y} -> ¬ (inj₁ x ⟨ ∼₁ ⊎-Rel ∼₂ ⟩₁ inj₂ y)
  ₁≁₂ ()

  drop-inj₁ :  forall {a₁} -> {∼₁ : Rel a₁}
            -> forall {a₂} -> {∼₂ : Rel a₂}
            -> forall {x y}
            -> inj₁ x ⟨ ∼₁ ⊎-Rel ∼₂ ⟩₁ inj₁ y -> ∼₁ x y
  drop-inj₁ (inj₁-Rel x∼y) = x∼y

  drop-inj₂ :  forall {a₁} -> {∼₁ : Rel a₁}
            -> forall {a₂} -> {∼₂ : Rel a₂}
            -> forall {x y}
            -> inj₂ x ⟨ ∼₁ ⊎-Rel ∼₂ ⟩₁ inj₂ y -> ∼₂ x y
  drop-inj₂ (inj₂-Rel x∼y) = x∼y

  ₂≰₁ :  forall {a₁} -> {≤₁ : Rel a₁}
      -> forall {a₂} -> {≤₂ : Rel a₂}
      -> forall {x y} -> ¬ (inj₂ x ⟨ ≤₁ ⊎-≤ ≤₂ ⟩₁ inj₁ y)
  ₂≰₁ ()

  drop-₁≤₁ :  forall {a₁} -> {≤₁ : Rel a₁}
           -> forall {a₂} -> {≤₂ : Rel a₂}
           -> forall {x y}
           -> inj₁ x ⟨ ≤₁ ⊎-≤ ≤₂ ⟩₁ inj₁ y -> ≤₁ x y
  drop-₁≤₁ (₁≤₁ x≤y) = x≤y

  drop-₂≤₂ :  forall {a₁} -> {≤₁ : Rel a₁}
           -> forall {a₂} -> {≤₂ : Rel a₂}
           -> forall {x y}
           -> inj₂ x ⟨ ≤₁ ⊎-≤ ≤₂ ⟩₁ inj₂ y -> ≤₂ x y
  drop-₂≤₂ (₂≤₂ x≤y) = x≤y

------------------------------------------------------------------------
-- Some properties are preserved

abstract

  _⊎-reflexive_
    :  forall {a₁} -> {≈₁ ∼₁ : Rel a₁} -> Reflexive ≈₁ ∼₁
    -> forall {a₂} -> {≈₂ ∼₂ : Rel a₂} -> Reflexive ≈₂ ∼₂
    -> Reflexive (≈₁ ⊎-Rel ≈₂) (∼₁ ⊎-Rel ∼₂)
  refl₁ ⊎-reflexive refl₂ = refl
    where
    refl : Reflexive (_ ⊎-Rel _) (_ ⊎-Rel _)
    refl (inj₁-Rel x₁≈y₁) = inj₁-Rel (refl₁ x₁≈y₁)
    refl (inj₂-Rel x₂≈y₂) = inj₂-Rel (refl₂ x₂≈y₂)

  _⊎-reflexive-≡_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Reflexive _≡_ ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Reflexive _≡_ ∼₂
    -> Reflexive _≡_ (∼₁ ⊎-Rel ∼₂)
  refl₁ ⊎-reflexive-≡ refl₂ = refl
    where
    refl : Reflexive _≡_ (_ ⊎-Rel _)
    refl {inj₁ x} ≡-refl = inj₁-Rel (refl₁ ≡-refl)
    refl {inj₂ y} ≡-refl = inj₂-Rel (refl₂ ≡-refl)

  _⊎-≤-reflexive_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> Reflexive ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> Reflexive ≈₂ ≤₂
    -> Reflexive (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-≤ ≤₂)
  refl₁ ⊎-≤-reflexive refl₂ = refl
    where
    refl : Reflexive (_ ⊎-Rel _) (_ ⊎-≤ _)
    refl (inj₁-Rel x₁≈y₁) = ₁≤₁ (refl₁ x₁≈y₁)
    refl (inj₂-Rel x₂≈y₂) = ₂≤₂ (refl₂ x₂≈y₂)

  _⊎-≤-irreflexive_
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁} -> Irreflexive ≈₁ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂} -> Irreflexive ≈₂ <₂
    -> Irreflexive (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-≤ <₂)
  irrefl₁ ⊎-≤-irreflexive irrefl₂ = irrefl
    where
    irrefl : Irreflexive (_ ⊎-Rel _) (_ ⊎-≤ _)
    irrefl (inj₁-Rel x₁≈y₁) (₁≤₁ x₁<y₁) = irrefl₁ x₁≈y₁ x₁<y₁
    irrefl (inj₂-Rel x₂≈y₂) (₂≤₂ x₂<y₂) = irrefl₂ x₂≈y₂ x₂<y₂

  _⊎-symmetric_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Symmetric ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Symmetric ∼₂
    -> Symmetric (∼₁ ⊎-Rel ∼₂)
  sym₁ ⊎-symmetric sym₂ = sym
    where
    sym : Symmetric (_ ⊎-Rel _)
    sym (inj₁-Rel x₁∼y₁) = inj₁-Rel (sym₁ x₁∼y₁)
    sym (inj₂-Rel x₂∼y₂) = inj₂-Rel (sym₂ x₂∼y₂)

  _⊎-transitive_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Transitive ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Transitive ∼₂
    -> Transitive (∼₁ ⊎-Rel ∼₂)
  trans₁ ⊎-transitive trans₂ = trans
    where
    trans : Transitive (_ ⊎-Rel _)
    trans (inj₁-Rel x∼y) (inj₁-Rel y∼z) = inj₁-Rel (trans₁ x∼y y∼z)
    trans (inj₂-Rel x∼y) (inj₂-Rel y∼z) = inj₂-Rel (trans₂ x∼y y∼z)

  _⊎-≤-transitive_
    :  forall {a₁} -> {≤₁ : Rel a₁} -> Transitive ≤₁
    -> forall {a₂} -> {≤₂ : Rel a₂} -> Transitive ≤₂
    -> Transitive (≤₁ ⊎-≤ ≤₂)
  trans₁ ⊎-≤-transitive trans₂ = trans
    where
    trans : Transitive (_ ⊎-≤ _)
    trans (₁≤₁ x₁≤y₁) (₁≤₁ y₁≤z₁) = ₁≤₁ (trans₁ x₁≤y₁ y₁≤z₁)
    trans (₂≤₂ x₂≤y₂) (₂≤₂ y₂≤z₂) = ₂≤₂ (trans₂ x₂≤y₂ y₂≤z₂)
    trans ₁≤₂         (₂≤₂ _)     = ₁≤₂
    trans (₁≤₁ _)     ₁≤₂         = ₁≤₂

  _⊎-antisymmetric_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> Antisymmetric ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> Antisymmetric ≈₂ ≤₂
    -> Antisymmetric (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-Rel ≤₂)
  antisym₁ ⊎-antisymmetric antisym₂ = antisym
    where
    antisym : Antisymmetric (_ ⊎-Rel _) (_ ⊎-Rel _)
    antisym (inj₁-Rel x≤y) (inj₁-Rel y≤x) = inj₁-Rel (antisym₁ x≤y y≤x)
    antisym (inj₂-Rel x≤y) (inj₂-Rel y≤x) = inj₂-Rel (antisym₂ x≤y y≤x)

  _⊎-≤-antisymmetric_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> Antisymmetric ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> Antisymmetric ≈₂ ≤₂
    -> Antisymmetric (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-≤ ≤₂)
  antisym₁ ⊎-≤-antisymmetric antisym₂ = antisym
    where
    antisym : Antisymmetric (_ ⊎-Rel _) (_ ⊎-≤ _)
    antisym (₁≤₁ x≤y) (₁≤₁ y≤x) = inj₁-Rel (antisym₁ x≤y y≤x)
    antisym (₂≤₂ x≤y) (₂≤₂ y≤x) = inj₂-Rel (antisym₂ x≤y y≤x)

  _⊎-≤-asymmetric_
    :  forall {a₁} -> {<₁ : Rel a₁} -> Asymmetric <₁
    -> forall {a₂} -> {<₂ : Rel a₂} -> Asymmetric <₂
    -> Asymmetric (<₁ ⊎-≤ <₂)
  asym₁ ⊎-≤-asymmetric asym₂ = asym
    where
    asym : Asymmetric (_ ⊎-≤ _)
    asym (₁≤₁ x<y) (₁≤₁ y<x) = asym₁ x<y y<x
    asym (₂≤₂ x<y) (₂≤₂ y<x) = asym₂ x<y y<x

  _⊎-≈-respects₂_
    :  forall {a₁} -> {≈₁ ∼₁ : Rel a₁}
    -> ≈₁ Respects₂ ∼₁
    -> forall {a₂} -> {≈₂ ∼₂ : Rel a₂}
    -> ≈₂ Respects₂ ∼₂
    -> (≈₁ ⊎-Rel ≈₂) Respects₂ (∼₁ ⊎-Rel ∼₂)
  _⊎-≈-respects₂_ {≈₁ = ≈₁} {∼₁ = ∼₁} resp₁
                  {≈₂ = ≈₂} {∼₂ = ∼₂} resp₂ =
    (\{_ _ _} -> resp¹) ,
    (\{_ _ _} -> resp²)
    where
    resp¹ : forall {x} -> (≈₁ ⊎-Rel ≈₂) Respects ((∼₁ ⊎-Rel ∼₂) x)
    resp¹ (inj₁-Rel y≈y') (inj₁-Rel x∼y) =
      inj₁-Rel (proj₁ resp₁ y≈y' x∼y)
    resp¹ (inj₂-Rel y≈y') (inj₂-Rel x∼y) =
      inj₂-Rel (proj₁ resp₂ y≈y' x∼y)

    resp² :  forall {y}
          -> (≈₁ ⊎-Rel ≈₂) Respects (flip₁ (∼₁ ⊎-Rel ∼₂) y)
    resp² (inj₁-Rel x≈x') (inj₁-Rel x∼y) =
      inj₁-Rel (proj₂ resp₁ x≈x' x∼y)
    resp² (inj₂-Rel x≈x') (inj₂-Rel x∼y) =
      inj₂-Rel (proj₂ resp₂ x≈x' x∼y)

  _⊎-≤-≈-respects₂_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁}
    -> ≈₁ Respects₂ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂}
    -> ≈₂ Respects₂ ≤₂
    -> (≈₁ ⊎-Rel ≈₂) Respects₂ (≤₁ ⊎-≤ ≤₂)
  _⊎-≤-≈-respects₂_ {≈₁ = ≈₁} {≤₁ = ≤₁} resp₁
                    {≈₂ = ≈₂} {≤₂ = ≤₂} resp₂ =
    (\{_ _ _} -> resp¹) ,
    (\{_ _ _} -> resp²)
    where
    resp¹ : forall {x} -> (≈₁ ⊎-Rel ≈₂) Respects ((≤₁ ⊎-≤ ≤₂) x)
    resp¹ (inj₁-Rel y≈y') (₁≤₁ x≤y) = ₁≤₁ (proj₁ resp₁ y≈y' x≤y)
    resp¹ (inj₂-Rel y≈y') (₂≤₂ x≤y) = ₂≤₂ (proj₁ resp₂ y≈y' x≤y)
    resp¹ (inj₂-Rel y≈y') ₁≤₂       = ₁≤₂

    resp² : forall {y} -> (≈₁ ⊎-Rel ≈₂) Respects (flip₁ (≤₁ ⊎-≤ ≤₂) y)
    resp² (inj₁-Rel x≈x') (₁≤₁ x≤y) = ₁≤₁ (proj₂ resp₁ x≈x' x≤y)
    resp² (inj₂-Rel x≈x') (₂≤₂ x≤y) = ₂≤₂ (proj₂ resp₂ x≈x' x≤y)
    resp² (inj₁-Rel x≈x') ₁≤₂       = ₁≤₂

  _⊎-substitutive_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Substitutive ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Substitutive ∼₂
    -> Substitutive (∼₁ ⊎-Rel ∼₂)
  subst₁ ⊎-substitutive subst₂ = subst
    where
    subst : Substitutive (_ ⊎-Rel _)
    subst P (inj₁-Rel x∼y) Px = subst₁ (\z -> P (inj₁ z)) x∼y Px
    subst P (inj₂-Rel x∼y) Px = subst₂ (\z -> P (inj₂ z)) x∼y Px

  _⊎-decidable_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Decidable ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Decidable ∼₂
    -> Decidable (∼₁ ⊎-Rel ∼₂)
  dec₁ ⊎-decidable dec₂ = dec
    where
    dec : Decidable (_ ⊎-Rel _)
    dec (inj₁ x) (inj₁ y) with dec₁ x y
    dec (inj₁ x) (inj₁ y) | yes x∼y = yes (inj₁-Rel x∼y)
    dec (inj₁ x) (inj₁ y) | no  x≁y = no (x≁y ∘ drop-inj₁)
    dec (inj₂ x) (inj₂ y) with dec₂ x y
    dec (inj₂ x) (inj₂ y) | yes x∼y = yes (inj₂-Rel x∼y)
    dec (inj₂ x) (inj₂ y) | no  x≁y = no (x≁y ∘ drop-inj₂)
    dec (inj₁ x) (inj₂ y) = no ₁≁₂
    dec (inj₂ x) (inj₁ y) = no ₂≁₁

  _⊎-≤-decidable_
    :  forall {a₁} -> {≤₁ : Rel a₁} -> Decidable ≤₁
    -> forall {a₂} -> {≤₂ : Rel a₂} -> Decidable ≤₂
    -> Decidable (≤₁ ⊎-≤ ≤₂)
  dec₁ ⊎-≤-decidable dec₂ = dec
    where
    dec : Decidable (_ ⊎-≤ _)
    dec (inj₁ x) (inj₂ y) = yes ₁≤₂
    dec (inj₂ x) (inj₁ y) = no  ₂≰₁
    dec (inj₁ x) (inj₁ y) with dec₁ x y
    dec (inj₁ x) (inj₁ y) | yes x∼y = yes (₁≤₁ x∼y)
    dec (inj₁ x) (inj₁ y) | no  x≁y = no (x≁y ∘ drop-₁≤₁)
    dec (inj₂ x) (inj₂ y) with dec₂ x y
    dec (inj₂ x) (inj₂ y) | yes x∼y = yes (₂≤₂ x∼y)
    dec (inj₂ x) (inj₂ y) | no  x≁y = no (x≁y ∘ drop-₂≤₂)

  _⊎-≤-total_
    :  forall {a₁} -> {≤₁ : Rel a₁} -> Total ≤₁
    -> forall {a₂} -> {≤₂ : Rel a₂} -> Total ≤₂
    -> Total (≤₁ ⊎-≤ ≤₂)
  total₁ ⊎-≤-total total₂ = total
    where
    total : Total (_ ⊎-≤ _)
    total (inj₁ x) (inj₁ y) = map-⊎ ₁≤₁ ₁≤₁ $ total₁ x y
    total (inj₂ x) (inj₂ y) = map-⊎ ₂≤₂ ₂≤₂ $ total₂ x y
    total (inj₁ x) (inj₂ y) = inj₁ ₁≤₂
    total (inj₂ x) (inj₁ y) = inj₂ ₁≤₂

  _⊎-≤-trichotomous_
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁} -> Trichotomous ≈₁ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂} -> Trichotomous ≈₂ <₂
    -> Trichotomous (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-≤ <₂)
  tri₁ ⊎-≤-trichotomous tri₂ = tri
    where
    tri : Trichotomous (_ ⊎-Rel _) (_ ⊎-≤ _)
    tri (inj₁ x) (inj₂ y) = Tri₁ ₁≤₂ ₁≁₂ ₂≰₁
    tri (inj₂ x) (inj₁ y) = Tri₃ ₂≰₁ ₂≁₁ ₁≤₂
    tri (inj₁ x) (inj₁ y) with tri₁ x y
    tri (inj₁ x) (inj₁ y) | Tri₁ x<y x≉y x≯y =
      Tri₁ (₁≤₁ x<y)        (x≉y ∘ drop-inj₁) (x≯y ∘ drop-₁≤₁)
    tri (inj₁ x) (inj₁ y) | Tri₂ x≮y x≈y x≯y =
      Tri₂ (x≮y ∘ drop-₁≤₁) (inj₁-Rel x≈y)    (x≯y ∘ drop-₁≤₁)
    tri (inj₁ x) (inj₁ y) | Tri₃ x≮y x≉y x>y =
      Tri₃ (x≮y ∘ drop-₁≤₁) (x≉y ∘ drop-inj₁) (₁≤₁ x>y)
    tri (inj₂ x) (inj₂ y) with tri₂ x y
    tri (inj₂ x) (inj₂ y) | Tri₁ x<y x≉y x≯y =
      Tri₁ (₂≤₂ x<y)        (x≉y ∘ drop-inj₂) (x≯y ∘ drop-₂≤₂)
    tri (inj₂ x) (inj₂ y) | Tri₂ x≮y x≈y x≯y =
      Tri₂ (x≮y ∘ drop-₂≤₂) (inj₂-Rel x≈y)    (x≯y ∘ drop-₂≤₂)
    tri (inj₂ x) (inj₂ y) | Tri₃ x≮y x≉y x>y =
      Tri₃ (x≮y ∘ drop-₂≤₂) (x≉y ∘ drop-inj₂) (₂≤₂ x>y)

------------------------------------------------------------------------
-- Some collections of properties are also preserved

abstract

  _⊎-preorder_
    :  forall {a₁} -> {≈₁ ∼₁ : Rel a₁} -> Preorder ≈₁ ∼₁
    -> forall {a₂} -> {≈₂ ∼₂ : Rel a₂} -> Preorder ≈₂ ∼₂
    -> Preorder (≈₁ ⊎-Rel ≈₂) (∼₁ ⊎-Rel ∼₂)
  pre₁ ⊎-preorder pre₂ = record
    { refl  = refl  pre₁ ⊎-reflexive  refl  pre₂
    ; trans = trans pre₁ ⊎-transitive trans pre₂
    }
    where open Preorder

  _⊎-preorder-≡_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> Preorder _≡_ ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> Preorder _≡_ ∼₂
    -> Preorder _≡_ (∼₁ ⊎-Rel ∼₂)
  pre₁ ⊎-preorder-≡ pre₂ = record
    { refl  = refl  pre₁ ⊎-reflexive-≡ refl  pre₂
    ; trans = trans pre₁ ⊎-transitive  trans pre₂
    }
    where open Preorder

  _⊎-equivalence_
    :  forall {a₁} -> {≈₁ : Rel a₁} -> Equivalence ≈₁
    -> forall {a₂} -> {≈₂ : Rel a₂} -> Equivalence ≈₂
    -> Equivalence (≈₁ ⊎-Rel ≈₂)
  eq₁ ⊎-equivalence eq₂ = record
    { preorder = preorder eq₁ ⊎-preorder-≡ preorder eq₂
    ; sym      = sym      eq₁ ⊎-symmetric  sym      eq₂
    }
    where open Equivalence

  _⊎-partialOrder_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> PartialOrder ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> PartialOrder ≈₂ ≤₂
    -> PartialOrder (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-Rel ≤₂)
  po₁ ⊎-partialOrder po₂ = record
    { equiv    = equiv    po₁ ⊎-equivalence   equiv    po₂
    ; preorder = preorder po₁ ⊎-preorder      preorder po₂
    ; antisym  = antisym  po₁ ⊎-antisymmetric antisym  po₂
    ; ≈-resp-≤ = ≈-resp-≤ po₁ ⊎-≈-respects₂   ≈-resp-≤ po₂
    }
    where open PartialOrder

  _⊎-≤-preorder_
    :  forall {a₁} -> {≈₁ ∼₁ : Rel a₁} -> Preorder ≈₁ ∼₁
    -> forall {a₂} -> {≈₂ ∼₂ : Rel a₂} -> Preorder ≈₂ ∼₂
    -> Preorder (≈₁ ⊎-Rel ≈₂) (∼₁ ⊎-≤ ∼₂)
  pre₁ ⊎-≤-preorder pre₂ = record
    { refl  = refl  pre₁ ⊎-≤-reflexive  refl  pre₂
    ; trans = trans pre₁ ⊎-≤-transitive trans pre₂
    }
    where open Preorder

  _⊎-≤-partialOrder_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> PartialOrder ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> PartialOrder ≈₂ ≤₂
    -> PartialOrder (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-≤ ≤₂)
  po₁ ⊎-≤-partialOrder po₂ = record
    { equiv    = equiv    po₁ ⊎-equivalence     equiv    po₂
    ; preorder = preorder po₁ ⊎-≤-preorder      preorder po₂
    ; antisym  = antisym  po₁ ⊎-≤-antisymmetric antisym  po₂
    ; ≈-resp-≤ = ≈-resp-≤ po₁ ⊎-≤-≈-respects₂   ≈-resp-≤ po₂
    }
    where open PartialOrder

  _⊎-≤-strictPartialOrder_
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁} -> StrictPartialOrder ≈₁ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂} -> StrictPartialOrder ≈₂ <₂
    -> StrictPartialOrder (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-≤ <₂)
  spo₁ ⊎-≤-strictPartialOrder spo₂ = record
    { equiv    = equiv    spo₁ ⊎-equivalence   equiv    spo₂
    ; irrefl   = irrefl   spo₁ ⊎-≤-irreflexive irrefl   spo₂
    ; trans    = trans    spo₁ ⊎-≤-transitive  trans    spo₂
    ; ≈-resp-< = ≈-resp-< spo₁ ⊎-≤-≈-respects₂ ≈-resp-< spo₂
    }
    where open StrictPartialOrder

------------------------------------------------------------------------
-- And the game can be taken even further...

_⊎-setoid_ : Setoid -> Setoid -> Setoid
s₁ ⊎-setoid s₂ = record
  { carrier = carrier s₁ ⊎             carrier s₂
  ; _≈_     = _≈_     s₁ ⊎-Rel         _≈_     s₂
  ; equiv   = equiv   s₁ ⊎-equivalence equiv   s₂
  }
  where open Setoid

_⊎-decSetoid_ : DecSetoid -> DecSetoid -> DecSetoid
ds₁ ⊎-decSetoid ds₂ = record
  { setoid = setoid ds₁ ⊎-setoid    setoid ds₂
  ; _≟_    = _≟_    ds₁ ⊎-decidable _≟_    ds₂
  }
  where open DecSetoid

_⊎-poset_ : Poset -> Poset -> Poset
po₁ ⊎-poset po₂ = record
  { carrier  = carrier  po₁ ⊎              carrier  po₂
  ; _≈_      = _≈_      po₁ ⊎-Rel          _≈_      po₂
  ; _≤_      = _≤_      po₁ ⊎-Rel          _≤_      po₂
  ; ord      = ord      po₁ ⊎-partialOrder ord      po₂
  }
  where
  open Poset
  open PartialOrder

_⊎-≤-poset_ : Poset -> Poset -> Poset
po₁ ⊎-≤-poset po₂ = record
  { carrier  = carrier  po₁ ⊎                carrier  po₂
  ; _≈_      = _≈_      po₁ ⊎-Rel            _≈_      po₂
  ; _≤_      = _≤_      po₁ ⊎-≤              _≤_      po₂
  ; ord      = ord      po₁ ⊎-≤-partialOrder ord      po₂
  }
  where
  open Poset
  open PartialOrder

_⊎-decTotOrder_ : DecTotOrder -> DecTotOrder -> DecTotOrder
dto₁ ⊎-decTotOrder dto₂ = record
  { poset = poset dto₁ ⊎-≤-poset     poset dto₂
  ; _≟_   = _≟_   dto₁ ⊎-decidable   _≟_   dto₂
  ; _≤?_  = _≤?_  dto₁ ⊎-≤-decidable _≤?_  dto₂
  ; total = total dto₁ ⊎-≤-total     total dto₂
  }
  where
  open DecTotOrder
