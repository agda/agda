------------------------------------------------------------------------
-- Lists where at least one element satisfies a given property
------------------------------------------------------------------------

module Data.List.Any where

open import Data.Empty
open import Data.Function
open import Data.List as List hiding (map; any)
open import Data.Product as Prod using (∃; _×_; _,_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Pred; _⊆_)
open import Relation.Binary.PropositionalEquality

-- Any P xs means that at least one element in xs satisfies P.

data Any {A} (P : A → Set) : List A → Set where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

-- List membership.

infix 4 _∈_ _∉_

_∈_ : ∀ {A} → A → List A → Set
x ∈ xs = Any (_≡_ x) xs

_∉_ : ∀ {A} → A → List A → Set
x ∉ xs = ¬ x ∈ xs

find : ∀ {A} {P : A → Set} {xs} → Any P xs → ∃ λ x → x ∈ xs × P x
find (here px)   = (_ , here refl , px)
find (there pxs) = Prod.map id (Prod.map there id) (find pxs)

gmap : ∀ {A B} {P : A → Set} {Q : B → Set} {f : A → B} →
       P ⊆ Q ∘₀ f → Any P ⊆ Any Q ∘₀ List.map f
gmap g (here px)   = here (g px)
gmap g (there pxs) = there (gmap g pxs)

map : ∀ {A} {P Q : Pred A} → P ⊆ Q → Any P ⊆ Any Q
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

any : ∀ {A} {P : A → Set} →
      (∀ x → Dec (P x)) → (xs : List A) → Dec (Any P xs)
any p []       = no λ()
any p (x ∷ xs) with p x
any p (x ∷ xs) | yes px = yes (here px)
any p (x ∷ xs) | no ¬px = Dec.map (there , helper) (any p xs)
  where
  helper : Any _ (x ∷ xs) → Any _ xs
  helper (here  px)  = ⊥-elim (¬px px)
  helper (there pxs) = pxs
