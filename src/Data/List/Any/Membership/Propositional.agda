------------------------------------------------------------------------
-- The Agda standard library
--
-- Data.List.Any.Membership instantiated with propositional equality,
-- along with some additional definitions.
------------------------------------------------------------------------

module Data.List.Any.Membership.Propositional where

open import Data.Empty
open import Data.Fin
open import Function.Inverse using (_↔_)
open import Function.Related as Related hiding (_∼[_]_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Any using (Any; map)
import Data.List.Any.Membership as Membership
open import Data.Product as Prod using (∃; _×_; _,_; uncurry′; proj₂)
open import Relation.Nullary
open import Relation.Binary hiding (Decidable)
import Relation.Binary.InducedPreorders as Ind
open import Relation.Binary.List.Pointwise as ListEq using ([]; _∷_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_)

private module M {a} {A : Set a} = Membership (PropEq.setoid A)
open M public hiding (lose)

lose : ∀ {a p} {A : Set a} {P : A → Set p} {x xs} →
       x ∈ xs → P x → Any P xs
lose {P = P} = M.lose (PropEq.subst P)

-- _⊆_ is a preorder.

⊆-preorder : ∀ {a} → Set a → Preorder _ _ _
⊆-preorder A = Ind.InducedPreorder₂ (PropEq.setoid (List A)) _∈_
                                      (PropEq.subst (_∈_ _))

-- Set and bag equality and related preorders.

open Related public
  using (Kind; Symmetric-kind)
   renaming ( implication         to subset
            ; reverse-implication to superset
            ; equivalence         to set
            ; injection           to subbag
            ; reverse-injection   to superbag
            ; bijection           to bag
            )

[_]-Order : Kind → ∀ {a} → Set a → Preorder _ _ _
[ k ]-Order A = Related.InducedPreorder₂ k (_∈_ {A = A})

[_]-Equality : Symmetric-kind → ∀ {a} → Set a → Setoid _ _
[ k ]-Equality A = Related.InducedEquivalence₂ k (_∈_ {A = A})

infix 4 _∼[_]_

_∼[_]_ : ∀ {a} {A : Set a} → List A → Kind → List A → Set _
_∼[_]_ {A = A} xs k ys = Preorder._∼_ ([ k ]-Order A) xs ys

-- Bag equality implies the other relations.

bag-=⇒ : ∀ {k a} {A : Set a} {xs ys : List A} →
         xs ∼[ bag ] ys → xs ∼[ k ] ys
bag-=⇒ xs≈ys = ↔⇒ xs≈ys

-- "Equational" reasoning for _⊆_.

module ⊆-Reasoning where
  import Relation.Binary.PreorderReasoning as PreR
  private
    open module PR {a} {A : Set a} = PreR (⊆-preorder A) public
      renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _≈⟨_⟩_ to _≡⟨_⟩_)

  infixr 2 _∼⟨_⟩_
  infix  1 _∈⟨_⟩_

  _∈⟨_⟩_ : ∀ {a} {A : Set a} x {xs ys : List A} →
           x ∈ xs → xs IsRelatedTo ys → x ∈ ys
  x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

  _∼⟨_⟩_ : ∀ {k a} {A : Set a} xs {ys zs : List A} →
           xs ∼[ ⌊ k ⌋→ ] ys → ys IsRelatedTo zs → xs IsRelatedTo zs
  xs ∼⟨ xs≈ys ⟩ ys≈zs = xs ⊆⟨ ⇒→ xs≈ys ⟩ ys≈zs
