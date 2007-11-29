------------------------------------------------------------------------
-- Sums of binary relations
------------------------------------------------------------------------

module Relation.Binary.Sum where

open import Logic
open import Data.Function
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

infixr 1 _⊎-Rel_ _⊎-<_

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

-- All things to the left are smaller than (or equal to, depending on
-- the underlying equality) all things to the right.

data _⊎-<_ {a₁ : Set} (_<₁_ : Rel a₁)
           {a₂ : Set} (_<₂_ : Rel a₂)
         : a₁ ⊎ a₂ -> a₁ ⊎ a₂ -> Set where
  ₁<₂ : forall {x y}           -> (_<₁_ ⊎-< _<₂_) (inj₁ x) (inj₂ y)
  ₁<₁ : forall {x y} -> x <₁ y -> (_<₁_ ⊎-< _<₂_) (inj₁ x) (inj₁ y)
  ₂<₂ : forall {x y} -> x <₂ y -> (_<₁_ ⊎-< _<₂_) (inj₂ x) (inj₂ y)

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
      -> forall {x y} -> ¬ (inj₂ x ⟨ ≤₁ ⊎-< ≤₂ ⟩₁ inj₁ y)
  ₂≰₁ ()

  drop-₁<₁ :  forall {a₁} -> {≤₁ : Rel a₁}
           -> forall {a₂} -> {≤₂ : Rel a₂}
           -> forall {x y}
           -> inj₁ x ⟨ ≤₁ ⊎-< ≤₂ ⟩₁ inj₁ y -> ≤₁ x y
  drop-₁<₁ (₁<₁ x≤y) = x≤y

  drop-₂<₂ :  forall {a₁} -> {≤₁ : Rel a₁}
           -> forall {a₂} -> {≤₂ : Rel a₂}
           -> forall {x y}
           -> inj₂ x ⟨ ≤₁ ⊎-< ≤₂ ⟩₁ inj₂ y -> ≤₂ x y
  drop-₂<₂ (₂<₂ x≤y) = x≤y

------------------------------------------------------------------------
-- Some properties which are preserved by the relation formers above

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

  _⊎-<-reflexive_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> Reflexive ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> Reflexive ≈₂ ≤₂
    -> Reflexive (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-< ≤₂)
  refl₁ ⊎-<-reflexive refl₂ = refl
    where
    refl : Reflexive (_ ⊎-Rel _) (_ ⊎-< _)
    refl (inj₁-Rel x₁≈y₁) = ₁<₁ (refl₁ x₁≈y₁)
    refl (inj₂-Rel x₂≈y₂) = ₂<₂ (refl₂ x₂≈y₂)

  _⊎-irreflexive_
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁} -> Irreflexive ≈₁ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂} -> Irreflexive ≈₂ <₂
    -> Irreflexive (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-Rel <₂)
  irrefl₁ ⊎-irreflexive irrefl₂ = irrefl
    where
    irrefl : Irreflexive (_ ⊎-Rel _) (_ ⊎-Rel _)
    irrefl (inj₁-Rel x₁≈y₁) (inj₁-Rel x₁<y₁) = irrefl₁ x₁≈y₁ x₁<y₁
    irrefl (inj₂-Rel x₂≈y₂) (inj₂-Rel x₂<y₂) = irrefl₂ x₂≈y₂ x₂<y₂

  _⊎-<-irreflexive_
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁} -> Irreflexive ≈₁ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂} -> Irreflexive ≈₂ <₂
    -> Irreflexive (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-< <₂)
  irrefl₁ ⊎-<-irreflexive irrefl₂ = irrefl
    where
    irrefl : Irreflexive (_ ⊎-Rel _) (_ ⊎-< _)
    irrefl (inj₁-Rel x₁≈y₁) (₁<₁ x₁<y₁) = irrefl₁ x₁≈y₁ x₁<y₁
    irrefl (inj₂-Rel x₂≈y₂) (₂<₂ x₂<y₂) = irrefl₂ x₂≈y₂ x₂<y₂

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

  _⊎-<-transitive_
    :  forall {a₁} -> {≤₁ : Rel a₁} -> Transitive ≤₁
    -> forall {a₂} -> {≤₂ : Rel a₂} -> Transitive ≤₂
    -> Transitive (≤₁ ⊎-< ≤₂)
  trans₁ ⊎-<-transitive trans₂ = trans
    where
    trans : Transitive (_ ⊎-< _)
    trans (₁<₁ x₁≤y₁) (₁<₁ y₁≤z₁) = ₁<₁ (trans₁ x₁≤y₁ y₁≤z₁)
    trans (₂<₂ x₂≤y₂) (₂<₂ y₂≤z₂) = ₂<₂ (trans₂ x₂≤y₂ y₂≤z₂)
    trans ₁<₂         (₂<₂ _)     = ₁<₂
    trans (₁<₁ _)     ₁<₂         = ₁<₂

  _⊎-antisymmetric_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> Antisymmetric ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> Antisymmetric ≈₂ ≤₂
    -> Antisymmetric (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-Rel ≤₂)
  antisym₁ ⊎-antisymmetric antisym₂ = antisym
    where
    antisym : Antisymmetric (_ ⊎-Rel _) (_ ⊎-Rel _)
    antisym (inj₁-Rel x≤y) (inj₁-Rel y≤x) = inj₁-Rel (antisym₁ x≤y y≤x)
    antisym (inj₂-Rel x≤y) (inj₂-Rel y≤x) = inj₂-Rel (antisym₂ x≤y y≤x)

  _⊎-<-antisymmetric_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> Antisymmetric ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> Antisymmetric ≈₂ ≤₂
    -> Antisymmetric (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-< ≤₂)
  antisym₁ ⊎-<-antisymmetric antisym₂ = antisym
    where
    antisym : Antisymmetric (_ ⊎-Rel _) (_ ⊎-< _)
    antisym (₁<₁ x≤y) (₁<₁ y≤x) = inj₁-Rel (antisym₁ x≤y y≤x)
    antisym (₂<₂ x≤y) (₂<₂ y≤x) = inj₂-Rel (antisym₂ x≤y y≤x)
    antisym ₁<₂       ()

  _⊎-asymmetric_
    :  forall {a₁} -> {<₁ : Rel a₁} -> Asymmetric <₁
    -> forall {a₂} -> {<₂ : Rel a₂} -> Asymmetric <₂
    -> Asymmetric (<₁ ⊎-Rel <₂)
  asym₁ ⊎-asymmetric asym₂ = asym
    where
    asym : Asymmetric (_ ⊎-Rel _)
    asym (inj₁-Rel x<y) (inj₁-Rel y<x) = asym₁ x<y y<x
    asym (inj₂-Rel x<y) (inj₂-Rel y<x) = asym₂ x<y y<x

  _⊎-<-asymmetric_
    :  forall {a₁} -> {<₁ : Rel a₁} -> Asymmetric <₁
    -> forall {a₂} -> {<₂ : Rel a₂} -> Asymmetric <₂
    -> Asymmetric (<₁ ⊎-< <₂)
  asym₁ ⊎-<-asymmetric asym₂ = asym
    where
    asym : Asymmetric (_ ⊎-< _)
    asym (₁<₁ x<y) (₁<₁ y<x) = asym₁ x<y y<x
    asym (₂<₂ x<y) (₂<₂ y<x) = asym₂ x<y y<x
    asym ₁<₂       ()

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

  _⊎-<-≈-respects₂_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁}
    -> ≈₁ Respects₂ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂}
    -> ≈₂ Respects₂ ≤₂
    -> (≈₁ ⊎-Rel ≈₂) Respects₂ (≤₁ ⊎-< ≤₂)
  _⊎-<-≈-respects₂_ {≈₁ = ≈₁} {≤₁ = ≤₁} resp₁
                    {≈₂ = ≈₂} {≤₂ = ≤₂} resp₂ =
    (\{_ _ _} -> resp¹) ,
    (\{_ _ _} -> resp²)
    where
    resp¹ : forall {x} -> (≈₁ ⊎-Rel ≈₂) Respects ((≤₁ ⊎-< ≤₂) x)
    resp¹ (inj₁-Rel y≈y') (₁<₁ x≤y) = ₁<₁ (proj₁ resp₁ y≈y' x≤y)
    resp¹ (inj₂-Rel y≈y') (₂<₂ x≤y) = ₂<₂ (proj₁ resp₂ y≈y' x≤y)
    resp¹ (inj₂-Rel y≈y') ₁<₂       = ₁<₂

    resp² : forall {y} -> (≈₁ ⊎-Rel ≈₂) Respects (flip₁ (≤₁ ⊎-< ≤₂) y)
    resp² (inj₁-Rel x≈x') (₁<₁ x≤y) = ₁<₁ (proj₂ resp₁ x≈x' x≤y)
    resp² (inj₂-Rel x≈x') (₂<₂ x≤y) = ₂<₂ (proj₂ resp₂ x≈x' x≤y)
    resp² (inj₁-Rel x≈x') ₁<₂       = ₁<₂

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
  _⊎-decidable_ {∼₁ = ∼₁} dec₁ {∼₂ = ∼₂} dec₂ = dec
    where
    dec : Decidable (∼₁ ⊎-Rel ∼₂)
    dec (inj₁ x) (inj₁ y) with dec₁ x y
    ...                   | yes x∼y = yes (inj₁-Rel x∼y)
    ...                   | no  x≁y = no (x≁y ∘ drop-inj₁)
    dec (inj₂ x) (inj₂ y) with dec₂ x y
    ...                   | yes x∼y = yes (inj₂-Rel x∼y)
    ...                   | no  x≁y = no (x≁y ∘ drop-inj₂)
    dec (inj₁ x) (inj₂ y) = no ₁≁₂
    dec (inj₂ x) (inj₁ y) = no ₂≁₁

  _⊎-<-decidable_
    :  forall {a₁} -> {≤₁ : Rel a₁} -> Decidable ≤₁
    -> forall {a₂} -> {≤₂ : Rel a₂} -> Decidable ≤₂
    -> Decidable (≤₁ ⊎-< ≤₂)
  _⊎-<-decidable_ {≤₁ = ≤₁} dec₁ {≤₂ = ≤₂} dec₂ = dec
    where
    dec : Decidable (≤₁ ⊎-< ≤₂)
    dec (inj₁ x) (inj₂ y) = yes ₁<₂
    dec (inj₂ x) (inj₁ y) = no  ₂≰₁
    dec (inj₁ x) (inj₁ y) with dec₁ x y
    ...                   | yes x∼y = yes (₁<₁ x∼y)
    ...                   | no  x≁y = no (x≁y ∘ drop-₁<₁)
    dec (inj₂ x) (inj₂ y) with dec₂ x y
    ...                   | yes x∼y = yes (₂<₂ x∼y)
    ...                   | no  x≁y = no (x≁y ∘ drop-₂<₂)

  _⊎-<-total_
    :  forall {a₁} -> {≤₁ : Rel a₁} -> Total ≤₁
    -> forall {a₂} -> {≤₂ : Rel a₂} -> Total ≤₂
    -> Total (≤₁ ⊎-< ≤₂)
  total₁ ⊎-<-total total₂ = total
    where
    total : Total (_ ⊎-< _)
    total (inj₁ x) (inj₁ y) = map-⊎ ₁<₁ ₁<₁ $ total₁ x y
    total (inj₂ x) (inj₂ y) = map-⊎ ₂<₂ ₂<₂ $ total₂ x y
    total (inj₁ x) (inj₂ y) = inj₁ ₁<₂
    total (inj₂ x) (inj₁ y) = inj₂ ₁<₂

  _⊎-<-trichotomous_
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁} -> Trichotomous ≈₁ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂} -> Trichotomous ≈₂ <₂
    -> Trichotomous (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-< <₂)
  _⊎-<-trichotomous_ {≈₁ = ≈₁} {<₁ = <₁} tri₁
                     {≈₂ = ≈₂} {<₂ = <₂} tri₂ = tri
    where
    tri : Trichotomous (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-< <₂)
    tri (inj₁ x) (inj₂ y) = Tri₁ ₁<₂ ₁≁₂ ₂≰₁
    tri (inj₂ x) (inj₁ y) = Tri₃ ₂≰₁ ₂≁₁ ₁<₂
    tri (inj₁ x) (inj₁ y) with tri₁ x y
    ...                   | Tri₁ x<y x≉y x≯y =
      Tri₁ (₁<₁ x<y)        (x≉y ∘ drop-inj₁) (x≯y ∘ drop-₁<₁)
    ...                   | Tri₂ x≮y x≈y x≯y =
      Tri₂ (x≮y ∘ drop-₁<₁) (inj₁-Rel x≈y)    (x≯y ∘ drop-₁<₁)
    ...                   | Tri₃ x≮y x≉y x>y =
      Tri₃ (x≮y ∘ drop-₁<₁) (x≉y ∘ drop-inj₁) (₁<₁ x>y)
    tri (inj₂ x) (inj₂ y) with tri₂ x y
    ...                   | Tri₁ x<y x≉y x≯y =
      Tri₁ (₂<₂ x<y)        (x≉y ∘ drop-inj₂) (x≯y ∘ drop-₂<₂)
    ...                   | Tri₂ x≮y x≈y x≯y =
      Tri₂ (x≮y ∘ drop-₂<₂) (inj₂-Rel x≈y)    (x≯y ∘ drop-₂<₂)
    ...                   | Tri₃ x≮y x≉y x>y =
      Tri₃ (x≮y ∘ drop-₂<₂) (x≉y ∘ drop-inj₂) (₂<₂ x>y)

------------------------------------------------------------------------
-- Some collections of properties which are preserved

abstract

  _⊎-isEquivalence_
    :  forall {a₁} -> {≈₁ : Rel a₁} -> IsEquivalence ≈₁
    -> forall {a₂} -> {≈₂ : Rel a₂} -> IsEquivalence ≈₂
    -> IsEquivalence (≈₁ ⊎-Rel ≈₂)
  eq₁ ⊎-isEquivalence eq₂ = record
    { refl  = refl  eq₁ ⊎-reflexive-≡ refl  eq₂
    ; sym   = sym   eq₁ ⊎-symmetric   sym   eq₂
    ; trans = trans eq₁ ⊎-transitive  trans eq₂
    }
    where open IsEquivalence

  _⊎-isPreorder_
    :  forall {a₁} -> {≈₁ ∼₁ : Rel a₁} -> IsPreorder ≈₁ ∼₁
    -> forall {a₂} -> {≈₂ ∼₂ : Rel a₂} -> IsPreorder ≈₂ ∼₂
    -> IsPreorder (≈₁ ⊎-Rel ≈₂) (∼₁ ⊎-Rel ∼₂)
  pre₁ ⊎-isPreorder pre₂ = record
    { isEquivalence = isEquivalence pre₁ ⊎-isEquivalence
                      isEquivalence pre₂
    ; refl          = refl     pre₁ ⊎-reflexive   refl     pre₂
    ; trans         = trans    pre₁ ⊎-transitive  trans    pre₂
    ; ≈-resp-∼      = ≈-resp-∼ pre₁ ⊎-≈-respects₂ ≈-resp-∼ pre₂
    }
    where open IsPreorder

  _⊎-isPreorder-≡_
    :  forall {a₁} -> {∼₁ : Rel a₁} -> IsPreorder _≡_ ∼₁
    -> forall {a₂} -> {∼₂ : Rel a₂} -> IsPreorder _≡_ ∼₂
    -> IsPreorder _≡_ (∼₁ ⊎-Rel ∼₂)
  pre₁ ⊎-isPreorder-≡ pre₂ = record
    { isEquivalence = ≡-isEquivalence
    ; refl          = refl  pre₁ ⊎-reflexive-≡ refl  pre₂
    ; trans         = trans pre₁ ⊎-transitive  trans pre₂
    ; ≈-resp-∼      = ≡-resp _
    }
    where open IsPreorder

  _⊎-isDecEquivalence_
    :  forall {a₁} -> {≈₁ : Rel a₁} -> IsDecEquivalence ≈₁
    -> forall {a₂} -> {≈₂ : Rel a₂} -> IsDecEquivalence ≈₂
    -> IsDecEquivalence (≈₁ ⊎-Rel ≈₂)
  eq₁ ⊎-isDecEquivalence eq₂ = record
    { isEquivalence = isEquivalence eq₁ ⊎-isEquivalence
                      isEquivalence eq₂
    ; decidable     = decidable eq₁ ⊎-decidable decidable eq₂
    }
    where open IsDecEquivalence

  _⊎-isPartialOrder_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> IsPartialOrder ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> IsPartialOrder ≈₂ ≤₂
    -> IsPartialOrder (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-Rel ≤₂)
  po₁ ⊎-isPartialOrder po₂ = record
    { isPreorder = isPreorder po₁ ⊎-isPreorder    isPreorder po₂
    ; antisym    = antisym    po₁ ⊎-antisymmetric antisym    po₂
    }
    where open IsPartialOrder

  _⊎-<-isPreorder_
    :  forall {a₁} -> {≈₁ ∼₁ : Rel a₁} -> IsPreorder ≈₁ ∼₁
    -> forall {a₂} -> {≈₂ ∼₂ : Rel a₂} -> IsPreorder ≈₂ ∼₂
    -> IsPreorder (≈₁ ⊎-Rel ≈₂) (∼₁ ⊎-< ∼₂)
  pre₁ ⊎-<-isPreorder pre₂ = record
    { isEquivalence = isEquivalence pre₁ ⊎-isEquivalence
                      isEquivalence pre₂
    ; refl          = refl     pre₁ ⊎-<-reflexive   refl     pre₂
    ; trans         = trans    pre₁ ⊎-<-transitive  trans    pre₂
    ; ≈-resp-∼      = ≈-resp-∼ pre₁ ⊎-<-≈-respects₂ ≈-resp-∼ pre₂
    }
    where open IsPreorder

  _⊎-<-isPartialOrder_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> IsPartialOrder ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> IsPartialOrder ≈₂ ≤₂
    -> IsPartialOrder (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-< ≤₂)
  po₁ ⊎-<-isPartialOrder po₂ = record
    { isPreorder = isPreorder po₁ ⊎-<-isPreorder    isPreorder po₂
    ; antisym    = antisym    po₁ ⊎-<-antisymmetric antisym    po₂
    }
    where open IsPartialOrder

  _⊎-<-isStrictPartialOrder_
    :  forall {a₁} -> {≈₁ <₁ : Rel a₁} -> IsStrictPartialOrder ≈₁ <₁
    -> forall {a₂} -> {≈₂ <₂ : Rel a₂} -> IsStrictPartialOrder ≈₂ <₂
    -> IsStrictPartialOrder (≈₁ ⊎-Rel ≈₂) (<₁ ⊎-< <₂)
  spo₁ ⊎-<-isStrictPartialOrder spo₂ = record
    { isEquivalence = isEquivalence spo₁ ⊎-isEquivalence
                      isEquivalence spo₂
    ; irrefl        = irrefl   spo₁ ⊎-<-irreflexive irrefl   spo₂
    ; trans         = trans    spo₁ ⊎-<-transitive  trans    spo₂
    ; ≈-resp-<      = ≈-resp-< spo₁ ⊎-<-≈-respects₂ ≈-resp-< spo₂
    }
    where open IsStrictPartialOrder

  _⊎-<-isTotalOrder_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> IsTotalOrder ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> IsTotalOrder ≈₂ ≤₂
    -> IsTotalOrder (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-< ≤₂)
  to₁ ⊎-<-isTotalOrder to₂ = record
    { isPartialOrder = isPartialOrder to₁ ⊎-<-isPartialOrder
                       isPartialOrder to₂
    ; total          = total to₁ ⊎-<-total total to₂
    }
    where open IsTotalOrder

  _⊎-<-isDecTotalOrder_
    :  forall {a₁} -> {≈₁ ≤₁ : Rel a₁} -> IsDecTotalOrder ≈₁ ≤₁
    -> forall {a₂} -> {≈₂ ≤₂ : Rel a₂} -> IsDecTotalOrder ≈₂ ≤₂
    -> IsDecTotalOrder (≈₁ ⊎-Rel ≈₂) (≤₁ ⊎-< ≤₂)
  to₁ ⊎-<-isDecTotalOrder to₂ = record
    { isTotalOrder = isTotalOrder to₁ ⊎-<-isTotalOrder isTotalOrder to₂
    ; ≈-decidable  = ≈-decidable  to₁ ⊎-decidable      ≈-decidable  to₂
    ; ≤-decidable  = ≤-decidable  to₁ ⊎-<-decidable    ≤-decidable  to₂
    }
    where open IsDecTotalOrder

------------------------------------------------------------------------
-- The game can be taken even further...

_⊎-setoid_ : Setoid -> Setoid -> Setoid
s₁ ⊎-setoid s₂ = record
  { carrier       = carrier       s₁ ⊎               carrier       s₂
  ; eq            = eq            s₁ ⊎-Rel           eq            s₂
  ; isEquivalence = isEquivalence s₁ ⊎-isEquivalence isEquivalence s₂
  }
  where open Setoid

_⊎-preorder_ : Preorder -> Preorder -> Preorder
p₁ ⊎-preorder p₂ = record
  { carrier      = carrier      p₁ ⊎            carrier      p₂
  ; underlyingEq = underlyingEq p₁ ⊎-Rel        underlyingEq p₂
  ; rel          = rel          p₁ ⊎-Rel        rel          p₂
  ; isPreorder   = isPreorder   p₁ ⊎-isPreorder isPreorder   p₂
  }
  where open Preorder

_⊎-decSetoid_ : DecSetoid -> DecSetoid -> DecSetoid
ds₁ ⊎-decSetoid ds₂ = record
  { carrier          = carrier ds₁ ⊎     carrier ds₂
  ; eq               = eq      ds₁ ⊎-Rel eq      ds₂
  ; isDecEquivalence = isDecEquivalence ds₁ ⊎-isDecEquivalence
                       isDecEquivalence ds₂
  }
  where open DecSetoid

_⊎-poset_ : Poset -> Poset -> Poset
po₁ ⊎-poset po₂ = record
  { carrier        = carrier        po₁ ⊎     carrier      po₂
  ; underlyingEq   = underlyingEq   po₁ ⊎-Rel underlyingEq po₂
  ; order          = order          po₁ ⊎-Rel order        po₂
  ; isPartialOrder = isPartialOrder po₁ ⊎-isPartialOrder
                     isPartialOrder po₂
  }
  where
  open Poset

_⊎-<-poset_ : Poset -> Poset -> Poset
po₁ ⊎-<-poset po₂ = record
  { carrier        = carrier        po₁ ⊎     carrier      po₂
  ; underlyingEq   = underlyingEq   po₁ ⊎-Rel underlyingEq po₂
  ; order          = order          po₁ ⊎-<   order        po₂
  ; isPartialOrder = isPartialOrder po₁ ⊎-<-isPartialOrder
                     isPartialOrder po₂
  }
  where
  open Poset

_⊎-<-strictPartialOrder_
  : StrictPartialOrder -> StrictPartialOrder -> StrictPartialOrder
spo₁ ⊎-<-strictPartialOrder spo₂ = record
  { carrier              = carrier      spo₁ ⊎     carrier      spo₂
  ; underlyingEq         = underlyingEq spo₁ ⊎-Rel underlyingEq spo₂
  ; order                = order        spo₁ ⊎-<   order        spo₂
  ; isStrictPartialOrder = isStrictPartialOrder spo₁
                             ⊎-<-isStrictPartialOrder
                           isStrictPartialOrder spo₂
  }
  where
  open StrictPartialOrder

_⊎-<-totalOrder_
  : TotalOrder -> TotalOrder -> TotalOrder
to₁ ⊎-<-totalOrder to₂ = record
  { carrier      = carrier      to₁ ⊎                carrier      to₂
  ; underlyingEq = underlyingEq to₁ ⊎-Rel            underlyingEq to₂
  ; order        = order        to₁ ⊎-<              order        to₂
  ; isTotalOrder = isTotalOrder to₁ ⊎-<-isTotalOrder isTotalOrder to₂
  }
  where
  open TotalOrder

_⊎-<-decTotalOrder_
  : DecTotalOrder -> DecTotalOrder -> DecTotalOrder
to₁ ⊎-<-decTotalOrder to₂ = record
  { carrier         = carrier      to₁ ⊎     carrier      to₂
  ; underlyingEq    = underlyingEq to₁ ⊎-Rel underlyingEq to₂
  ; order           = order        to₁ ⊎-<   order        to₂
  ; isDecTotalOrder = isDecTotalOrder to₁ ⊎-<-isDecTotalOrder
                      isDecTotalOrder to₂
  }
  where
  open DecTotalOrder
