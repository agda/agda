------------------------------------------------------------------------
-- Binary relations
------------------------------------------------------------------------

module Relation.Binary where

open import Logic
open import Data.Function
open import Data.Sum
open import Data.Product
open import Relation.Nullary

-- Binary relations.

Rel : Set -> Set1
Rel a = a -> a -> Set

------------------------------------------------------------------------
-- Properties

Reflexive : {a : Set} -> (_≈_ _∼_ : Rel a) -> Set
Reflexive _≈_ _∼_ = forall {x y} -> x ≈ y -> x ∼ y

Irreflexive : {a : Set} -> (_≈_ _<_ : Rel a) -> Set
Irreflexive _≈_ _<_ = forall {x y} -> x ≈ y -> ¬ (x < y)

Symmetric : {a : Set} -> Rel a -> Set
Symmetric _∼_ = forall {x y} -> x ∼ y -> y ∼ x

Transitive : {a : Set} -> Rel a -> Set
Transitive _∼_ = forall {x y z} -> x ∼ y -> y ∼ z -> x ∼ z

Antisymmetric : {a : Set} -> (_≈_ _≤_ : Rel a) -> Set
Antisymmetric _≈_ _≤_ = forall {x y} -> x ≤ y -> y ≤ x -> x ≈ y

Asymmetric : {a : Set} -> (_<_ : Rel a) -> Set
Asymmetric _<_ = forall {x y} -> x < y -> ¬ (y < x)

_Respects_ : {a : Set} -> Rel a -> (a -> Set) -> Set
_∼_ Respects P = forall {x y} -> x ∼ y -> P x -> P y

_Respects₂_ : {a : Set} -> Rel a -> Rel a -> Set
∼ Respects₂ P =
  (forall {x} -> ∼ Respects (P x)      ) ×
  (forall {y} -> ∼ Respects (flip₁ P y))

Substitutive : {a : Set} -> Rel a -> Set1
Substitutive {a} ∼ = (P : a -> Set) -> ∼ Respects P

_Preserves_→_ : forall {a₁ a₂} -> (a₁ -> a₂) -> Rel a₁ -> Rel a₂ -> Set
f Preserves _∼₁_ → _∼₂_ = forall {x y} -> x ∼₁ y -> f x ∼₂ f y

_Preserves₂_→_→_
  :  forall {a₁ a₂ a₃}
  -> (a₁ -> a₂ -> a₃) -> Rel a₁ -> Rel a₂ -> Rel a₃ -> Set
_+_ Preserves₂ _∼₁_ → _∼₂_ → _∼₃_ =
  forall {x y u v} -> x ∼₁ y -> u ∼₂ v -> (x + u) ∼₃ (y + v)

Congruential : ({a : Set} -> Rel a) -> Set1
Congruential ∼ = forall {a b} -> (f : a -> b) -> f Preserves ∼ → ∼

Congruential₂ : ({a : Set} -> Rel a) -> Set1
Congruential₂ ∼ =
  forall {a b c} -> (f : a -> b -> c) -> f Preserves₂ ∼ → ∼ → ∼

Decidable : {a : Set} -> Rel a -> Set
Decidable _∼_ = forall x y -> Dec (x ∼ y)

Total : {a : Set} -> Rel a -> Set
Total _∼_ = forall x y -> (x ∼ y) ⊎ (y ∼ x)

data Tri (a b c : Set) : Set where
  Tri₁ :   a -> ¬ b -> ¬ c -> Tri a b c
  Tri₂ : ¬ a ->   b -> ¬ c -> Tri a b c
  Tri₃ : ¬ a -> ¬ b ->   c -> Tri a b c

Trichotomous : {a : Set} -> Rel a -> Rel a -> Set
Trichotomous _≈_ _<_ = forall x y -> Tri (x < y) (x ≈ y) (x > y)
  where _>_ = flip₁ _<_

Monotone
  :  forall {a₁} -> (≤₁ : Rel a₁)
  -> forall {a₂} -> (≤₂ : Rel a₂)
  -> (a₁ -> a₂) -> Set
Monotone ≤₁ ≤₂ f = f Preserves ≤₁ → ≤₂

Monotone₂
  :  forall {a₁} -> (≤₁ : Rel a₁)
  -> forall {a₂} -> (≤₂ : Rel a₂)
  -> forall {a₃} -> (≤₃ : Rel a₃)
  -> (a₁ -> a₂ -> a₃) -> Set
Monotone₂ ≤₁ ≤₂ ≤₃ • = • Preserves₂ ≤₁ → ≤₂ → ≤₃

------------------------------------------------------------------------
-- Some properties imply others

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

subst⟶resp₂
  :  forall {a ∼} -> (P : Rel a)
  -> Substitutive ∼
  -> ∼ Respects₂ P
subst⟶resp₂ {∼ = ∼} P subst =
  (\{x _ _} y'∼y Pxy' -> subst (P x)         y'∼y Pxy') ,
  (\{y _ _} x'∼x Px'y -> subst (\x -> P x y) x'∼x Px'y)

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

------------------------------------------------------------------------
-- Interesting combinations of properties

record Preorder {a : Set} (_≈_ _∼_ : Rel a) : Set where
  refl  : Reflexive _≈_ _∼_
  trans : Transitive _∼_

record Equivalence {a : Set} (_≈_ : Rel a) : Set where
  preorder : Preorder _≡_ _≈_
  sym      : Symmetric _≈_

record PartialOrder {a : Set} (_≈_ _≤_ : Rel a) : Set where
  equiv    : Equivalence _≈_
  preorder : Preorder _≈_ _≤_
  antisym  : Antisymmetric _≈_ _≤_
  ≈-resp-≤ : _≈_ Respects₂ _≤_

record StrictPartialOrder {a : Set} (_≈_ _<_ : Rel a) : Set where
  equiv    : Equivalence _≈_
  irrefl   : Irreflexive _≈_ _<_
  trans    : Transitive _<_
  ≈-resp-< : _≈_ Respects₂ _<_

------------------------------------------------------------------------
-- Properties packaged up with sets and relations

-- Just a small selection of interesting combinations.

record PreSetoid : Set1 where
  carrier  : Set
  _∼_      : Rel carrier
  _≈_      : Rel carrier
  preorder : Preorder _≈_ _∼_
  equiv    : Equivalence _≈_

record Setoid : Set1 where
  carrier : Set
  _≈_     : Rel carrier
  equiv   : Equivalence _≈_

record DecSetoid : Set1 where
  setoid : Setoid
  _≟_    : Decidable (Setoid._≈_ setoid)

record Poset : Set1 where
  carrier  : Set
  _≈_      : Rel carrier
  _≤_      : Rel carrier
  ord      : PartialOrder _≈_ _≤_

open Poset

record DecTotOrder : Set1 where
  poset : Poset
  _≟_   : Decidable (_≈_ poset)
  _≤?_  : Decidable (_≤_ poset)
  total : Total (_≤_ poset)
