------------------------------------------------------------------------
-- The Agda standard library
--
-- List membership and some related definitions
------------------------------------------------------------------------

open import Level using (Level; _⊔_)
open import Relation.Binary hiding (Decidable)

module Data.List.Any.Membership {c ℓ : Level} (S : Setoid c ℓ) where

open import Function
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Any using (Any; map; here; there)
open import Data.Product as Prod using (∃; _×_; _,_)
open import Relation.Nullary using (¬_)
import Relation.Binary.InducedPreorders as Ind
open import Relation.Binary.List.Pointwise as ListEq using ([]; _∷_)

open Setoid S renaming (Carrier to A)
open Setoid (ListEq.setoid S) using () renaming (_≈_ to _≋_)


-- List membership.

infix 4 _∈_ _∉_

_∈_ : A → List A → Set _
x ∈ xs = Any (_≈_ x) xs

_∉_ : A → List A → Set _
x ∉ xs = ¬ x ∈ xs

-- Subsets.

infix 4 _⊆_ _⊈_

_⊆_ : List A → List A → Set _
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊈_ : List A → List A → Set _
xs ⊈ ys = ¬ xs ⊆ ys


-- If a predicate P respects the underlying equality then Any P
-- respects the list equality.

lift-resp : ∀ {p} {P : A → Set p} →
            P Respects _≈_ → Any P Respects _≋_
lift-resp resp []            ()
lift-resp resp (x≈y ∷ xs≈ys) (here px)   = here (resp x≈y px)
lift-resp resp (x≈y ∷ xs≈ys) (there pxs) =
  there (lift-resp resp xs≈ys pxs)

-- Equality is respected by the predicate which is used to define
-- _∈_.

∈-resp-≈ : ∀ {x} → (_≈_ x) Respects _≈_
∈-resp-≈ = flip trans

-- List equality is respected by _∈_.

∈-resp-list-≈ : ∀ {x} → _∈_ x Respects _≋_
∈-resp-list-≈ = lift-resp ∈-resp-≈

-- _⊆_ is a preorder.

⊆-preorder : Preorder _ _ _
⊆-preorder = Ind.InducedPreorder₂ (ListEq.setoid S) _∈_ ∈-resp-list-≈

module ⊆-Reasoning where
  import Relation.Binary.PreorderReasoning as PreR
  open PreR ⊆-preorder public
    renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

  infix 1 _∈⟨_⟩_

  _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
  x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

-- A variant of List.map.

map-with-∈ : ∀ {b} {B : Set b}
             (xs : List A) → (∀ {x} → x ∈ xs → B) → List B
map-with-∈ []       f = []
map-with-∈ (x ∷ xs) f = f (here refl) ∷ map-with-∈ xs (f ∘ there)

-- Finds an element satisfying the predicate.

find : ∀ {p} {P : A → Set p} {xs} →
       Any P xs → ∃ λ x → x ∈ xs × P x
find (here px)   = (_ , here refl , px)
find (there pxs) = Prod.map id (Prod.map there id) (find pxs)

lose : ∀ {p} {P : A → Set p} {x xs} →
       P Respects _≈_ → x ∈ xs → P x → Any P xs
lose resp x∈xs px = map (flip resp px) x∈xs
