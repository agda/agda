------------------------------------------------------------------------
-- Lists where all elements satisfy a given property
------------------------------------------------------------------------

module Data.List.All where

open import Data.Function
open import Data.List as List hiding (map; all)
open import Data.List.Any as Any using (here; there)
open Any.Membership-≡ using (_∈_; _⊆_)
open import Data.Product as Prod using (_,_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Pred) renaming (_⊆_ to _⋐_)
open import Relation.Binary.PropositionalEquality

-- All P xs means that all elements in xs satisfy P.

infixr 5 _∷_

data All {A} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

head : ∀ {A} {P : A → Set} {x xs} → All P (x ∷ xs) → P x
head (px ∷ pxs) = px

tail : ∀ {A} {P : A → Set} {x xs} → All P (x ∷ xs) → All P xs
tail (px ∷ pxs) = pxs

lookup : ∀ {A} {P : A → Set} {xs} → All P xs → (∀ {x} → x ∈ xs → P x)
lookup []         ()
lookup (px ∷ pxs) (here refl)  = px
lookup (px ∷ pxs) (there x∈xs) = lookup pxs x∈xs

tabulate : ∀ {A} {P : A → Set} {xs} → (∀ {x} → x ∈ xs → P x) → All P xs
tabulate {xs = []}     hyp = []
tabulate {xs = x ∷ xs} hyp = hyp (here refl) ∷ tabulate (hyp ∘ there)

map : ∀ {A} {P Q : Pred A} → P ⋐ Q → All P ⋐ All Q
map g []         = []
map g (px ∷ pxs) = g px ∷ map g pxs

all : ∀ {A} {P : A → Set} →
      (∀ x → Dec (P x)) → (xs : List A) → Dec (All P xs)
all p []       = yes []
all p (x ∷ xs) with p x
all p (x ∷ xs) | yes px = Dec.map (_∷_ px , tail) (all p xs)
all p (x ∷ xs) | no ¬px = no (¬px ∘ head)
