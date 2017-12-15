------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors where all elements satisfy a given property
------------------------------------------------------------------------

module Data.Vec.All where

open import Data.Vec as Vec using (Vec; []; _∷_; zip)
open import Data.Vec.Properties using (lookup-zip)
open import Data.Fin using (Fin; zero; suc)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Data.Product using (uncurry)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Decidable) renaming (_⊆_ to _⋐_)
open import Relation.Binary.PropositionalEquality using (subst)

------------------------------------------------------------------------
-- All P xs means that all elements in xs satisfy P.

infixr 5 _∷_

data All {a p} {A : Set a}
         (P : A → Set p) : ∀ {k} → Vec A k → Set (p ⊔ a) where
  []  : All P []
  _∷_ : ∀ {k x} {xs : Vec A k} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

head : ∀ {a p} {A : Set a} {P : A → Set p} {k x} {xs : Vec A k} →
       All P (x ∷ xs) → P x
head (px ∷ pxs) = px

tail : ∀ {a p} {A : Set a} {P : A → Set p} {k x} {xs : Vec A k} →
       All P (x ∷ xs) → All P xs
tail (px ∷ pxs) = pxs

lookup : ∀ {a p} {A : Set a} {P : A → Set p} {k} {xs : Vec A k} →
         (i : Fin k) → All P xs → P (Vec.lookup i xs)
lookup ()      []
lookup zero    (px ∷ pxs) = px
lookup (suc i) (px ∷ pxs) = lookup i pxs

tabulate : ∀ {a p} {A : Set a} {P : A → Set p} {k} {xs : Vec A k} →
           (∀ x → P x) → All P xs
tabulate {xs = []}     hyp = []
tabulate {xs = x ∷ xs} hyp = hyp x ∷ tabulate hyp

map : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {k} →
      P ⋐ Q → All P {k} ⋐ All Q {k}
map g []         = []
map g (px ∷ pxs) = g px ∷ map g pxs

all : ∀ {a p} {A : Set a} {P : A → Set p} {k} →
      Decidable P → Decidable (All P {k})
all p []       = yes []
all p (x ∷ xs) with p x
all p (x ∷ xs) | yes px = Dec.map′ (_∷_ px) tail (all p xs)
all p (x ∷ xs) | no ¬px = no (¬px ∘ head)

zipWith : ∀ {a b c p q r} {A : Set a} {B : Set b} {C : Set c} {_⊕_ : A → B → C}
          {P : A → Set p} {Q : B → Set q} {R : C → Set r} →
          (∀ {x y} → P x → Q y → R (x ⊕ y)) →
          ∀ {k xs ys} → All P {k} xs → All Q {k} ys →
          All R {k} (Vec.zipWith _⊕_ xs ys)
zipWith _⊕_ {xs = []}     {[]}     []         []         = []
zipWith _⊕_ {xs = x ∷ xs} {y ∷ ys} (px ∷ pxs) (qy ∷ qys) =
  px ⊕ qy ∷ zipWith _⊕_ pxs qys

------------------------------------------------------------------------
-- All₂ is DEPRECATED. Please use Data.Vec.Relation.InductivePointwise
-- directly.

open import Data.Vec.Relation.InductivePointwise using () renaming
  ( Pointwise to All₂
  ; lookup    to lookup₂
  ; map       to map₂
  ) public
