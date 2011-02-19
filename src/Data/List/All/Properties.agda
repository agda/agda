------------------------------------------------------------------------
-- Properties relating All to various list functions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.List.All.Properties where

open import Data.Bool
open import Data.Bool.Properties
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (module Equivalent)
open import Data.List as List
import Data.List.Any as Any
open Any.Membership-≡
open import Data.List.All as All using (All; []; _∷_)
open import Data.Product
open import Relation.Unary using () renaming (_⊆_ to _⋐_)

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
All-all p (px ∷ pxs) = Equivalent.from T-∧ ⟨$⟩ (px , All-all p pxs)

all-All : ∀ {a} {A : Set a} (p : A → Bool) xs →
          T (all p xs) → All (T ∘ p) xs
all-All p []       _     = []
all-All p (x ∷ xs) px∷xs with Equivalent.to (T-∧ {p x}) ⟨$⟩ px∷xs
all-All p (x ∷ xs) px∷xs | (px , pxs) = px ∷ all-All p xs pxs

-- All is anti-monotone.

anti-mono : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
            xs ⊆ ys → All P ys → All P xs
anti-mono xs⊆ys pys = All.tabulate (All.lookup pys ∘ xs⊆ys)

-- all is anti-monotone.

all-anti-mono : ∀ {a} {A : Set a} (p : A → Bool) {xs ys} →
                xs ⊆ ys → T (all p ys) → T (all p xs)
all-anti-mono p xs⊆ys = All-all p ∘ anti-mono xs⊆ys ∘ all-All p _
