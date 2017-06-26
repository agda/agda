------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where at least one element satisfies a given property
------------------------------------------------------------------------

module Data.List.Any where

open import Data.Empty
open import Data.Fin
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Equiv using (module Equivalence)
open import Function.Related as Related hiding (_∼[_]_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product as Prod using (∃; _×_; _,_)
open import Level using (Level; _⊔_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Decidable) renaming (_⊆_ to _⋐_)
open import Relation.Binary hiding (Decidable)
import Relation.Binary.InducedPreorders as Ind
open import Relation.Binary.List.Pointwise as ListEq using ([]; _∷_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_)

-- Any P xs means that at least one element in xs satisfies P.

data Any {a p} {A : Set a}
         (P : A → Set p) : List A → Set (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

-- Map.

map : ∀ {a p q} {A : Set a} {P : A → Set p} → {Q : A → Set q} →
      P ⋐ Q → Any P ⋐ Any Q
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

-- If the head does not satisfy the predicate, then the tail will.

tail : ∀ {a p} {A : Set a} {x : A} {xs : List A} {P : A → Set p} →
       ¬ P x → Any P (x ∷ xs) → Any P xs
tail ¬px (here  px)  = ⊥-elim (¬px px)
tail ¬px (there pxs) = pxs

-- Decides Any.

any : ∀ {a p} {A : Set a} {P : A → Set p} →
      Decidable P → Decidable (Any P)
any p []       = no λ()
any p (x ∷ xs) with p x
any p (x ∷ xs) | yes px = yes (here px)
any p (x ∷ xs) | no ¬px = Dec.map′ there (tail ¬px) (any p xs)

-- index x∈xs is the list position (zero-based) which x∈xs points to.

index : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
        Any P xs → Fin (List.length xs)
index (here  px)  = zero
index (there pxs) = suc (index pxs)

-- If any element satisfies P, then P is satisfied.

satisfied : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
            Any P xs → ∃ P
satisfied (here px) = _ , px
satisfied (there pxs) = satisfied pxs
