------------------------------------------------------------------------
-- Lists where at least one element satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.List.Any where

open import Data.Empty
open import Data.Fin
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Equiv using (module Equivalent)
open import Function.Inverse as Inv
  using (module Inverse)
open import Data.List as List using (List; []; _∷_)
open import Data.Product as Prod using (∃; _×_; _,_)
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using () renaming (_⊆_ to _⋐_)
open import Relation.Binary
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
      (∀ x → Dec (P x)) → (xs : List A) → Dec (Any P xs)
any p []       = no λ()
any p (x ∷ xs) with p x
any p (x ∷ xs) | yes px = yes (here px)
any p (x ∷ xs) | no ¬px = Dec.map′ there (tail ¬px) (any p xs)

-- index x∈xs is the list position (zero-based) which x∈xs points to.

index : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
        Any P xs → Fin (List.length xs)
index (here  px)  = zero
index (there pxs) = suc (index pxs)

------------------------------------------------------------------------
-- List membership and some related definitions

module Membership {c ℓ : Level} (S : Setoid c ℓ) where

  private
    open module  S = Setoid S using (_≈_) renaming (Carrier to A)
    open module LS = Setoid (ListEq.setoid S)
      using () renaming (_≈_ to _≋_)

  -- If a predicate P respects the underlying equality then Any P
  -- respects the list equality.

  lift-resp : ∀ {p} {P : A → Set p} →
              P Respects _≈_ → Any P Respects _≋_
  lift-resp resp []            ()
  lift-resp resp (x≈y ∷ xs≈ys) (here px)   = here (resp x≈y px)
  lift-resp resp (x≈y ∷ xs≈ys) (there pxs) =
    there (lift-resp resp xs≈ys pxs)

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

  -- Equality is respected by the predicate which is used to define
  -- _∈_.

  ∈-resp-≈ : ∀ {x} → (_≈_ x) Respects _≈_
  ∈-resp-≈ = flip S.trans

  -- List equality is respected by _∈_.

  ∈-resp-list-≈ : ∀ {x} → _∈_ x Respects _≋_
  ∈-resp-list-≈ = lift-resp ∈-resp-≈

  -- _⊆_ is a preorder.

  ⊆-preorder : Preorder _ _ _
  ⊆-preorder = Ind.InducedPreorder₂ (ListEq.setoid S) _∈_ ∈-resp-list-≈

  module ⊆-Reasoning where
    import Relation.Binary.PreorderReasoning as PreR
    open PreR ⊆-preorder public
      renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

    infix 1 _∈⟨_⟩_

    _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
    x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

  -- A variant of List.map.

  map-with-∈ : ∀ {b} {B : Set b}
               (xs : List A) → (∀ {x} → x ∈ xs → B) → List B
  map-with-∈ []       f = []
  map-with-∈ (x ∷ xs) f = f (here S.refl) ∷ map-with-∈ xs (f ∘ there)

  -- Finds an element satisfying the predicate.

  find : ∀ {p} {P : A → Set p} {xs} →
         Any P xs → ∃ λ x → x ∈ xs × P x
  find (here px)   = (_ , here S.refl , px)
  find (there pxs) = Prod.map id (Prod.map there id) (find pxs)

  lose : ∀ {p} {P : A → Set p} {x xs} →
         P Respects _≈_ → x ∈ xs → P x → Any P xs
  lose resp x∈xs px = map (flip resp px) x∈xs

-- The code above instantiated (and slightly changed) for
-- propositional equality, along with some additional definitions.

module Membership-≡ where

  private
    open module M {a} {A : Set a} = Membership (PropEq.setoid A) public
      hiding (lift-resp; lose; ⊆-preorder; module ⊆-Reasoning)

  lose : ∀ {a p} {A : Set a} {P : A → Set p} {x xs} →
         x ∈ xs → P x → Any P xs
  lose {P = P} = M.lose (PropEq.subst P)

  -- _⊆_ is a preorder.

  ⊆-preorder : ∀ {a} → Set a → Preorder _ _ _
  ⊆-preorder A = Ind.InducedPreorder₂ (PropEq.setoid (List A)) _∈_
                                      (PropEq.subst (_∈_ _))

  -- Set and bag equality.

  open Inv public
    using (Kind) renaming (equivalent to set; inverse to bag)

  [_]-Equality : Kind → ∀ {a} → Set a → Setoid _ _
  [ k ]-Equality A = Inv.InducedEquivalence₂ k (_∈_ {A = A})

  infix 4 _≈[_]_

  _≈[_]_ : ∀ {a} {A : Set a} → List A → Kind → List A → Set _
  _≈[_]_ {A = A} xs k ys = Setoid._≈_ ([ k ]-Equality A) xs ys

  -- Bag equality implies set equality.

  bag-=⇒set-= : ∀ {a} {A : Set a} {xs ys : List A} →
                xs ≈[ bag ] ys → xs ≈[ set ] ys
  bag-=⇒set-= xs≈ys = Inv.⇿⇒ xs≈ys

  -- "Equational" reasoning for _⊆_.

  module ⊆-Reasoning where
    import Relation.Binary.PreorderReasoning as PreR
    private
      open module PR {a} {A : Set a} = PreR (⊆-preorder A) public
        renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _≈⟨_⟩_ to _≡⟨_⟩_)

    infixr 2 _≈⟨_⟩_
    infix  1 _∈⟨_⟩_

    _∈⟨_⟩_ : ∀ {a} {A : Set a} x {xs ys : List A} →
             x ∈ xs → xs IsRelatedTo ys → x ∈ ys
    x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

    _≈⟨_⟩_ : ∀ {k a} {A : Set a} xs {ys zs : List A} →
             xs ≈[ k ] ys → ys IsRelatedTo zs → xs IsRelatedTo zs
    xs ≈⟨ xs≈ys ⟩ ys≈zs =
      xs ⊆⟨ _⟨$⟩_ (Equivalent.to (Inv.⇒⇔ xs≈ys)) ⟩ ys≈zs

------------------------------------------------------------------------
-- Another function

-- If any element satisfies P, then P is satisfied.

satisfied : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
            Any P xs → ∃ P
satisfied = Prod.map id Prod.proj₂ ∘ Membership-≡.find
