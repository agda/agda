------------------------------------------------------------------------
-- Lists where at least one element satisfies a given property
------------------------------------------------------------------------

module Data.List.Any where

open import Data.Empty
open import Data.Fin
open import Data.Function
open import Data.List as List hiding (map; any)
open import Data.Product as Prod using (∃; _×_; _,_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Pred) renaming (_⊆_ to _⋐_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq

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

-- Subsets.

infix 4 _⊆_ _⊈_

_⊆_ : ∀ {A} → List A → List A → Set
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊈_ : ∀ {A} → List A → List A → Set
xs ⊈ ys = ¬ xs ⊆ ys

-- _⊆_ is a preorder.

⊆-preorder : Set → Preorder
⊆-preorder A = record
  { carrier    = List A
  ; _≈_        = _≡_
  ; _∼_        = _⊆_
  ; isPreorder = record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive     = reflexive
    ; trans         = λ ys⊆zs xs⊆ys → xs⊆ys ∘ ys⊆zs
    ; ≈-resp-∼      = PropEq.resp _⊆_
    }
  }
  where
  reflexive : _≡_ ⇒ _⊆_
  reflexive refl = id

module ⊆-Reasoning {A : Set} where
  import Relation.Binary.PreorderReasoning as PreR
  open PreR (⊆-preorder A) public
    renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _≈⟨_⟩_ to _≡⟨_⟩_)

  infix 1 _∈⟨_⟩_

  _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
  x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

gmap : ∀ {A B} {P : A → Set} {Q : B → Set} {f : A → B} →
       P ⋐ Q ∘₀ f → Any P ⋐ Any Q ∘₀ List.map f
gmap g (here px)   = here (g px)
gmap g (there pxs) = there (gmap g pxs)

map : ∀ {A} {P Q : Pred A} → P ⋐ Q → Any P ⋐ Any Q
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

find : ∀ {A} {P : A → Set} {xs} → Any P xs → ∃ λ x → x ∈ xs × P x
find (here px)   = (_ , here refl , px)
find (there pxs) = Prod.map id (Prod.map there id) (find pxs)

lose : ∀ {A} {x xs} → x ∈ xs → {P : A → Set} → P x → Any P xs
lose x∈xs {P} px = map (flip (subst P) px) x∈xs

-- Any is monotone.

mono : ∀ {A} {P : Pred A} {xs ys} → xs ⊆ ys → Any P xs → Any P ys
mono xs⊆ys pxs with find pxs
... | (x , x∈xs , px) = lose (xs⊆ys x∈xs) px

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

index : ∀ {A} {P : A → Set} {xs} → Any P xs → Fin (length xs)
index (here  px)  = zero
index (there pxs) = suc (index pxs)
