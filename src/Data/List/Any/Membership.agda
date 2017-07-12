------------------------------------------------------------------------
-- The Agda standard library
--
-- List membership and some related definitions
------------------------------------------------------------------------

open import Relation.Binary hiding (Decidable)

module Data.List.Any.Membership {c ℓ} (S : Setoid c ℓ) where

open import Function using (_∘_; id; flip)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Any using (Any; map; here; there)
open import Data.Product as Prod using (∃; _×_; _,_)
open import Relation.Nullary using (¬_)

open Setoid S renaming (Carrier to A)

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
