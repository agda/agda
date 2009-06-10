------------------------------------------------------------------------
-- Conversion of < to ≤, along with a number of properties
------------------------------------------------------------------------

-- Possible TODO: Prove that a conversion ≤ → < → ≤ returns a
-- relation equivalent to the original one (and similarly for
-- < → ≤ → <).

open import Relation.Binary

module Relation.Binary.StrictToNonStrict
         {a : Set} (_≈_ _<_ : Rel a)
         where

open import Relation.Nullary
open import Relation.Binary.Consequences
open import Data.Function
open import Data.Product
open import Data.Sum
open import Data.Empty

------------------------------------------------------------------------
-- Conversion

-- _<_ can be turned into _≤_ as follows:

_≤_ : Rel a
x ≤ y = (x < y) ⊎ (x ≈ y)

------------------------------------------------------------------------
-- The converted relations have certain properties
-- (if the original relations have certain other properties)

reflexive : _≈_ ⇒ _≤_
reflexive = inj₂

antisym : IsEquivalence _≈_ →
          Transitive _<_ →
          Irreflexive _≈_ _<_ →
          Antisymmetric _≈_ _≤_
antisym eq trans irrefl = as
  where
  module Eq = IsEquivalence eq

  as : Antisymmetric _≈_ _≤_
  as (inj₂ x≈y) _          = x≈y
  as (inj₁ _)   (inj₂ y≈x) = Eq.sym y≈x
  as (inj₁ x<y) (inj₁ y<x) =
    ⊥-elim (trans∧irr⟶asym {≈ = _≈_} Eq.refl trans irrefl x<y y<x)

trans : IsEquivalence _≈_ → _<_ Respects₂ _≈_ →
        Transitive _<_ → Transitive _≤_
trans eq <-resp-≈ <-trans = tr
  where
  module Eq = IsEquivalence eq

  tr : Transitive _≤_
  tr (inj₁ x<y) (inj₁ y<z) = inj₁ $ <-trans x<y y<z
  tr (inj₁ x<y) (inj₂ y≈z) = inj₁ $ proj₁ <-resp-≈ y≈z x<y
  tr (inj₂ x≈y) (inj₁ y<z) = inj₁ $ proj₂ <-resp-≈ (Eq.sym x≈y) y<z
  tr (inj₂ x≈y) (inj₂ y≈z) = inj₂ $ Eq.trans x≈y y≈z

≤-resp-≈ : IsEquivalence _≈_ → _<_ Respects₂ _≈_ → _≤_ Respects₂ _≈_
≤-resp-≈ eq <-resp-≈ = ((λ {_ _ _} → resp₁) , (λ {_ _ _} → resp₂))
  where
  module Eq = IsEquivalence eq

  resp₁ : ∀ {x y' y} → y' ≈ y → x  ≤ y' → x ≤ y
  resp₁ y'≈y (inj₁ x<y') = inj₁ (proj₁ <-resp-≈ y'≈y x<y')
  resp₁ y'≈y (inj₂ x≈y') = inj₂ (Eq.trans x≈y' y'≈y)

  resp₂ : ∀ {y x' x} → x' ≈ x → x' ≤ y  → x ≤ y
  resp₂ x'≈x (inj₁ x'<y) = inj₁ (proj₂ <-resp-≈ x'≈x x'<y)
  resp₂ x'≈x (inj₂ x'≈y) = inj₂ (Eq.trans (Eq.sym x'≈x) x'≈y)

total : Trichotomous _≈_ _<_ → Total _≤_
total <-tri x y with <-tri x y
... | tri< x<y x≉y x≯y = inj₁ (inj₁ x<y)
... | tri≈ x≮y x≈y x≯y = inj₁ (inj₂ x≈y)
... | tri> x≮y x≉y x>y = inj₂ (inj₁ x>y)

decidable : Decidable _≈_ → Decidable _<_ → Decidable _≤_
decidable ≈-dec <-dec x y with ≈-dec x y | <-dec x y
... | yes x≈y | _       = yes (inj₂ x≈y)
... | no  x≉y | yes x<y = yes (inj₁ x<y)
... | no  x≉y | no  x≮y = no helper
  where
  helper : x ≤ y → ⊥
  helper (inj₁ x<y) = x≮y x<y
  helper (inj₂ x≈y) = x≉y x≈y

decidable' : Trichotomous _≈_ _<_ → Decidable _≤_
decidable' compare x y with compare x y
... | tri< x<y _   _ = yes (inj₁ x<y)
... | tri≈ _   x≈y _ = yes (inj₂ x≈y)
... | tri> x≮y x≉y _ = no helper
  where
  helper : x ≤ y → ⊥
  helper (inj₁ x<y) = x≮y x<y
  helper (inj₂ x≈y) = x≉y x≈y
