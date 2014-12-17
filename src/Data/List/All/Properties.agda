------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

module Data.List.All.Properties where

open import Data.Bool.Minimal using (Bool; T)
open import Data.Bool.Properties
open import Data.Empty
open import Data.List as List
import Data.List.Any as Any; open Any.Membership-≡
open import Data.List.All as All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.Product as Prod
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Function.Inverse using (_↔_)
open import Function.Surjection using (_↠_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Unary using (Decidable) renaming (_⊆_ to _⋐_)

-- Functions can be shifted between the predicate and the list.

All-map : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
            {f : A → B} {xs} →
          All (P ∘ f) xs → All P (List.map f xs)
All-map []       = []
All-map (p ∷ ps) = p ∷ All-map ps

map-All : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
            {f : A → B} {xs} →
          All P (List.map f xs) → All (P ∘ f) xs
map-All {xs = []}    []       = []
map-All {xs = _ ∷ _} (p ∷ ps) = p ∷ map-All ps

-- A variant of All.map.

gmap : ∀ {a b p q}
         {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
         {f : A → B} →
       P ⋐ Q ∘ f → All P ⋐ All Q ∘ List.map f
gmap g = All-map ∘ All.map g

-- All and all are related via T.

All-all : ∀ {a} {A : Set a} (p : A → Bool) {xs} →
          All (T ∘ p) xs → T (all p xs)
All-all p []         = _
All-all p (px ∷ pxs) = Equivalence.from T-∧ ⟨$⟩ (px , All-all p pxs)

all-All : ∀ {a} {A : Set a} (p : A → Bool) xs →
          T (all p xs) → All (T ∘ p) xs
all-All p []       _     = []
all-All p (x ∷ xs) px∷xs with Equivalence.to (T-∧ {p x}) ⟨$⟩ px∷xs
all-All p (x ∷ xs) px∷xs | (px , pxs) = px ∷ all-All p xs pxs

-- All is anti-monotone.

anti-mono : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
            xs ⊆ ys → All P ys → All P xs
anti-mono xs⊆ys pys = All.tabulate (All.lookup pys ∘ xs⊆ys)

-- all is anti-monotone.

all-anti-mono : ∀ {a} {A : Set a} (p : A → Bool) {xs ys} →
                xs ⊆ ys → T (all p ys) → T (all p xs)
all-anti-mono p xs⊆ys = All-all p ∘ anti-mono xs⊆ys ∘ all-All p _

-- All P (xs ++ ys) is isomorphic to All P xs and All P ys.

private

  ++⁺ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys : List A} →
        All P xs → All P ys → All P (xs ++ ys)
  ++⁺ []         pys = pys
  ++⁺ (px ∷ pxs) pys = px ∷ ++⁺ pxs pys

  ++⁻ : ∀ {a p} {A : Set a} {P : A → Set p} (xs : List A) {ys} →
        All P (xs ++ ys) → All P xs × All P ys
  ++⁻ []       p          = [] , p
  ++⁻ (x ∷ xs) (px ∷ pxs) = Prod.map (_∷_ px) id $ ++⁻ _ pxs

  ++⁺∘++⁻ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys}
            (p : All P (xs ++ ys)) → uncurry′ ++⁺ (++⁻ xs p) ≡ p
  ++⁺∘++⁻ []       p          = P.refl
  ++⁺∘++⁻ (x ∷ xs) (px ∷ pxs) = P.cong (_∷_ px) $ ++⁺∘++⁻ xs pxs

  ++⁻∘++⁺ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys}
            (p : All P xs × All P ys) → ++⁻ xs (uncurry ++⁺ p) ≡ p
  ++⁻∘++⁺ ([]       , pys) = P.refl
  ++⁻∘++⁺ (px ∷ pxs , pys) rewrite ++⁻∘++⁺ (pxs , pys) = P.refl

++↔ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
      (All P xs × All P ys) ↔ All P (xs ++ ys)
++↔ {P = P} {xs = xs} = record
  { to         = P.→-to-⟶ $ uncurry ++⁺
  ; from       = P.→-to-⟶ $ ++⁻ xs
  ; inverse-of = record
    { left-inverse-of  = ++⁻∘++⁺
    ; right-inverse-of = ++⁺∘++⁻ xs
    }
  }

-- Three lemmas relating Any, All and negation.

¬Any↠All¬ : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
            ¬ Any P xs ↠ All (¬_ ∘ P) xs
¬Any↠All¬ {P = P} = record
  { to         = P.→-to-⟶ (to _)
  ; surjective = record
    { from             = P.→-to-⟶ from
    ; right-inverse-of = to∘from
    }
  }
  where
  to : ∀ xs → ¬ Any P xs → All (¬_ ∘ P) xs
  to []       ¬p = []
  to (x ∷ xs) ¬p = ¬p ∘ here ∷ to xs (¬p ∘ there)

  from : ∀ {xs} → All (¬_ ∘ P) xs → ¬ Any P xs
  from []        ()
  from (¬p ∷ _)  (here  p) = ¬p p
  from (_  ∷ ¬p) (there p) = from ¬p p

  to∘from : ∀ {xs} (¬p : All (¬_ ∘ P) xs) → to xs (from ¬p) ≡ ¬p
  to∘from []         = P.refl
  to∘from (¬p ∷ ¬ps) = P.cong₂ _∷_ P.refl (to∘from ¬ps)

  -- If equality of functions were extensional, then the surjection
  -- could be strengthened to a bijection.

  from∘to : P.Extensionality _ _ →
            ∀ xs → (¬p : ¬ Any P xs) → from (to xs ¬p) ≡ ¬p
  from∘to ext []       ¬p = ext λ ()
  from∘to ext (x ∷ xs) ¬p = ext λ
    { (here p)  → P.refl
    ; (there p) → P.cong (λ f → f p) $ from∘to ext xs (¬p ∘ there)
    }

Any¬→¬All : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
            Any (¬_ ∘ P) xs → ¬ All P xs
Any¬→¬All (here  ¬p) = ¬p           ∘ All.head
Any¬→¬All (there ¬p) = Any¬→¬All ¬p ∘ All.tail

Any¬⇔¬All : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
            Decidable P → Any (¬_ ∘ P) xs ⇔ ¬ All P xs
Any¬⇔¬All {P = P} dec = record
  { to   = P.→-to-⟶ Any¬→¬All
  ; from = P.→-to-⟶ (from _)
  }
  where
  from : ∀ xs → ¬ All P xs → Any (¬_ ∘ P) xs
  from []       ¬∀ = ⊥-elim (¬∀ [])
  from (x ∷ xs) ¬∀ with dec x
  ... | yes p = there (from xs (¬∀ ∘ _∷_ p))
  ... | no ¬p = here ¬p

  -- If equality of functions were extensional, then the logical
  -- equivalence could be strengthened to a surjection.

  to∘from : P.Extensionality _ _ →
            ∀ {xs} (¬∀ : ¬ All P xs) → Any¬→¬All (from xs ¬∀) ≡ ¬∀
  to∘from ext ¬∀ = ext (⊥-elim ∘ ¬∀)
