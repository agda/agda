------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where at least one element satisfies a given property
------------------------------------------------------------------------

module Data.List.Any {a} {A : Set a} where

open import Data.Empty
open import Data.Fin
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product as Prod using (∃; _,_)
open import Level using (_⊔_)
open import Relation.Nullary using (¬_; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Decidable) renaming (_⊆_ to _⋐_)

-- Any P xs means that at least one element in xs satisfies P.

data Any {p} (P : A → Set p) : List A → Set (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

-- Map.

map : ∀ {p q} {P : A → Set p} {Q : A → Set q} → P ⋐ Q → Any P ⋐ Any Q
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

-- If the head does not satisfy the predicate, then the tail will.

tail : ∀ {p} {P : A → Set p} {x xs} → ¬ P x → Any P (x ∷ xs) → Any P xs
tail ¬px (here  px)  = ⊥-elim (¬px px)
tail ¬px (there pxs) = pxs

-- Decides Any.

any : ∀ {p} {P : A → Set p} → Decidable P → Decidable (Any P)
any p []       = no λ()
any p (x ∷ xs) with p x
any p (x ∷ xs) | yes px = yes (here px)
any p (x ∷ xs) | no ¬px = Dec.map′ there (tail ¬px) (any p xs)

-- index x∈xs is the list position (zero-based) which x∈xs points to.

index : ∀ {p} {P : A → Set p} {xs} → Any P xs → Fin (List.length xs)
index (here  px)  = zero
index (there pxs) = suc (index pxs)

-- If any element satisfies P, then P is satisfied.

satisfied : ∀ {p} {P : A → Set p} {xs} → Any P xs → ∃ P
satisfied (here px) = _ , px
satisfied (there pxs) = satisfied pxs
