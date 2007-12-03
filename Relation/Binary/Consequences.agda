------------------------------------------------------------------------
-- Some properties imply others
------------------------------------------------------------------------

module Relation.Binary.Consequences where

open import Relation.Binary
open import Relation.Nullary
open import Logic
open import Data.Function
open import Data.Sum
open import Data.Product

-- Some of the definitions can be found in the following module:

open import Relation.Binary.Consequences.Core public

trans∧irr⟶asym
  :  forall {a} -> {≈ < : Rel a}
  -> Reflexive _≡_ ≈
  -> Transitive < -> Irreflexive ≈ < -> Asymmetric <
trans∧irr⟶asym refl trans irrefl = \x<y y<x ->
  irrefl (refl ≡-refl) (trans x<y y<x)

irr∧antisym⟶asym
  :  forall {a} -> {≈ < : Rel a}
  -> Irreflexive ≈ < -> Antisymmetric ≈ < -> Asymmetric <
irr∧antisym⟶asym irrefl antisym = \x<y y<x ->
  irrefl (antisym x<y y<x) x<y

asym⟶antisym
  :  forall {a} -> {≈ < : Rel a}
  -> Asymmetric < -> Antisymmetric ≈ <
asym⟶antisym asym x<y y<x = ⊥-elim (asym x<y y<x)

asym⟶irr
  :  forall {a} -> {≈ < : Rel a}
  -> ≈ Respects₂ < -> Symmetric ≈
  -> Asymmetric < -> Irreflexive ≈ <
asym⟶irr {< = _<_} resp sym asym {x} {y} x≈y x<y = asym x<y y<x
  where
  y<y : y < y
  y<y = proj₂ resp x≈y x<y
  y<x : y < x
  y<x = proj₁ resp (sym x≈y) y<y

total⟶refl
  : forall {a} -> {≈ ∼ : Rel a}
  -> ≈ Respects₂ ∼ -> Symmetric ≈
  -> Total ∼ -> Reflexive ≈ ∼
total⟶refl {≈ = ≈} {∼ = ∼} resp sym total = refl
  where
  refl : Reflexive ≈ ∼
  refl {x} {y} x≈y with total x y
  ...              | inj₁ x∼y = x∼y
  ...              | inj₂ y∼x =
    proj₁ resp x≈y (proj₂ resp (sym x≈y) y∼x)

total+dec⟶dec
  : forall {a} -> {≈ ≤ : Rel a}
  -> Reflexive ≈ ≤ -> Antisymmetric ≈ ≤
  -> Total ≤ -> Decidable ≈ -> Decidable ≤
total+dec⟶dec {≈ = ≈} {≤ = ≤} refl antisym total _≟_ = dec
  where
  dec : Decidable ≤
  dec x y with total x y
  ... | inj₁ x≤y = yes x≤y
  ... | inj₂ y≤x with x ≟ y
  ...   | yes  x≈y = yes (refl x≈y)
  ...   | no  ¬x≈y = no (\x≤y -> ¬x≈y (antisym x≤y y≤x))

tri⟶asym : forall {a} -> {≈ < : Rel a}
         -> Trichotomous ≈ < -> Asymmetric <
tri⟶asym tri {x} {y} x<y x>y with tri x y
... | Tri₁ _   _ x≯y = x≯y x>y
... | Tri₂ _   _ x≯y = x≯y x>y
... | Tri₃ x≮y _ _   = x≮y x<y

subst⟶cong
  :  {≈ : forall {a} -> Rel a}
  -> (forall {a} -> Reflexive {a} _≡_ ≈)
  -> (forall {a} -> Substitutive {a} ≈)
  -> Congruential ≈
subst⟶cong {≈ = _≈_} refl subst f {x} x≈y =
  subst (\y -> f x ≈ f y) x≈y (refl ≡-refl)

cong+trans⟶cong₂
  :  {≈ : forall {a} -> Rel a}
  -> Congruential  ≈ -> (forall {a} -> Transitive {a} ≈)
  -> Congruential₂ ≈
cong+trans⟶cong₂ cong trans f {x = x} {v = v} x≈y u≈v =
  cong (f x) u≈v ⟨ trans ⟩ cong (flip f v) x≈y
