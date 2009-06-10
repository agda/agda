------------------------------------------------------------------------
-- Properties relating All to various list functions
------------------------------------------------------------------------

module Data.List.All.Properties where

open import Data.Bool
open import Data.Bool.Properties
open import Data.Function
open import Data.List as List
import Data.List.Any as Any
open Any.Membership-≡
open import Data.List.All as All using (All; []; _∷_)
open import Data.Product
open import Relation.Unary using (Pred) renaming (_⊆_ to _⋐_)

-- Functions can be shifted between the predicate and the list.

All-map : ∀ {A B} {P : Pred B} {f : A → B} {xs} →
          All (P ∘₀ f) xs → All P (List.map f xs)
All-map []       = []
All-map (p ∷ ps) = p ∷ All-map ps

map-All : ∀ {A B} {P : Pred B} {f : A → B} {xs} →
          All P (List.map f xs) → All (P ∘₀ f) xs
map-All {xs = []}    []       = []
map-All {xs = _ ∷ _} (p ∷ ps) = p ∷ map-All ps

-- A variant of All.map.

gmap : ∀ {A B} {P : A → Set} {Q : B → Set} {f : A → B} →
       P ⋐ Q ∘₀ f → All P ⋐ All Q ∘₀ List.map f
gmap g = All-map ∘ All.map g

-- All and all are related via T.

All-all : ∀ {A} (p : A → Bool) {xs} →
          All (T ∘₀ p) xs → T (all p xs)
All-all p []         = _
All-all p (px ∷ pxs) = proj₂ T-∧ (px , All-all p pxs)

all-All : ∀ {A} (p : A → Bool) xs →
          T (all p xs) → All (T ∘₀ p) xs
all-All p []       _     = []
all-All p (x ∷ xs) px∷xs with proj₁ (T-∧ {p x}) px∷xs
all-All p (x ∷ xs) px∷xs | (px , pxs) = px ∷ all-All p xs pxs

-- All is anti-monotone.

anti-mono : ∀ {A} {P : Pred A} {xs ys} → xs ⊆ ys → All P ys → All P xs
anti-mono xs⊆ys pys = All.tabulate (All.lookup pys ∘ xs⊆ys)

-- all is anti-monotone.

all-anti-mono : ∀ {A} (p : A → Bool) {xs ys} →
                xs ⊆ ys → T (all p ys) → T (all p xs)
all-anti-mono p xs⊆ys = All-all p ∘ anti-mono xs⊆ys ∘ all-All p _
