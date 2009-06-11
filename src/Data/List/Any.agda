------------------------------------------------------------------------
-- Lists where at least one element satisfies a given property
------------------------------------------------------------------------

module Data.List.Any where

open import Data.Empty
open import Data.Fin
open import Data.Function
open import Data.List as List using (List; []; _∷_)
import Data.List.Equality as ListEq
open import Data.Product as Prod using (∃; _×_; _,_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Pred) renaming (_⊆_ to _⋐_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_)

-- Any P xs means that at least one element in xs satisfies P.

data Any {A} (P : A → Set) : List A → Set where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

-- Map.

map : ∀ {A} {P Q : Pred A} → P ⋐ Q → Any P ⋐ Any Q
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

-- If the head does not satisfy the predicate, then the tail will.

tail : ∀ {A x xs} {P : A → Set} → ¬ P x → Any P (x ∷ xs) → Any P xs
tail ¬px (here  px)  = ⊥-elim (¬px px)
tail ¬px (there pxs) = pxs

-- Decides Any.

any : ∀ {A} {P : A → Set} →
      (∀ x → Dec (P x)) → (xs : List A) → Dec (Any P xs)
any p []       = no λ()
any p (x ∷ xs) with p x
any p (x ∷ xs) | yes px = yes (here px)
any p (x ∷ xs) | no ¬px = Dec.map (there , tail ¬px) (any p xs)

-- index x∈xs is the list position (zero-based) which x∈xs points to.

index : ∀ {A} {P : A → Set} {xs} → Any P xs → Fin (List.length xs)
index (here  px)  = zero
index (there pxs) = suc (index pxs)

------------------------------------------------------------------------
-- List membership and some related definitions

module Membership (S : Setoid) where

  private
    open module S = Setoid S using (_≈_) renaming (carrier to A)
    open module L = ListEq.Equality S
      using ([]; _∷_) renaming (_≈_ to _≋_)

  -- If a predicate P respects the underlying equality then Any P
  -- respects the list equality.

  lift-resp : ∀ {P} → P Respects _≈_ → Any P Respects _≋_
  lift-resp resp []            ()
  lift-resp resp (x≈y ∷ xs≈ys) (here px)   = here (resp x≈y px)
  lift-resp resp (x≈y ∷ xs≈ys) (there pxs) =
    there (lift-resp resp xs≈ys pxs)

  -- List membership.

  infix 4 _∈_ _∉_

  _∈_ : A → List A → Set
  x ∈ xs = Any (_≈_ x) xs

  _∉_ : A → List A → Set
  x ∉ xs = ¬ x ∈ xs

  -- Subsets.

  infix 4 _⊆_ _⊈_

  _⊆_ : List A → List A → Set
  xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

  _⊈_ : List A → List A → Set
  xs ⊈ ys = ¬ xs ⊆ ys

  -- Equality is respected by the predicate which is used to define
  -- _∈_.

  ∈-resp-≈ : ∀ {x} → (_≈_ x) Respects _≈_
  ∈-resp-≈ = flip S.trans

  -- List equality is respected by _∈_.

  ∈-resp-list-≈ : ∀ {x} → _∈_ x Respects _≋_
  ∈-resp-list-≈ = lift-resp ∈-resp-≈

  -- _⊆_ is a preorder.

  ⊆-preorder : Preorder
  ⊆-preorder = record
    { carrier    = List A
    ; _≈_        = _≋_
    ; _∼_        = _⊆_
    ; isPreorder = record
      { isEquivalence = Setoid.isEquivalence L.setoid
      ; reflexive     = reflexive
      ; trans         = λ ys⊆zs xs⊆ys → xs⊆ys ∘ ys⊆zs
      ; ∼-resp-≈      =
          (λ ys₁≋ys₂ xs⊆ys₁ → reflexive ys₁≋ys₂ ∘ xs⊆ys₁)
        , (λ xs₁≋xs₂ xs₁⊆ys → xs₁⊆ys ∘ reflexive (L.sym xs₁≋xs₂))
      }
    }
    where
    reflexive : _≋_ ⇒ _⊆_
    reflexive eq = ∈-resp-list-≈ eq

  module ⊆-Reasoning where
    import Relation.Binary.PreorderReasoning as PreR
    open PreR ⊆-preorder public
      renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

    infix 1 _∈⟨_⟩_

    _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
    x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

  -- A variant of List.map.

  map-with-∈ : ∀ {B} (xs : List A) → (∀ {x} → x ∈ xs → B) → List B
  map-with-∈ []       f = []
  map-with-∈ (x ∷ xs) f = f (here S.refl) ∷ map-with-∈ xs (f ∘ there)

  -- Finds an element satisfying the predicate.

  find : ∀ {P : A → Set} {xs} → Any P xs → ∃ λ x → x ∈ xs × P x
  find (here px)   = (_ , here S.refl , px)
  find (there pxs) = Prod.map id (Prod.map there id) (find pxs)

  lose : ∀ {P x xs} → P Respects _≈_ → x ∈ xs → P x → Any P xs
  lose resp x∈xs px = map (flip resp px) x∈xs

-- The code above instantiated (and slightly changed) for
-- propositional equality.

module Membership-≡ {A : Set} where

  private
    open module M = Membership (PropEq.setoid A) public
      hiding (lift-resp; lose; ⊆-preorder; module ⊆-Reasoning)

  lose : ∀ {P x xs} → x ∈ xs → P x → Any P xs
  lose {P} = M.lose (PropEq.subst P)

  -- _⊆_ is a preorder.

  ⊆-preorder : Preorder
  ⊆-preorder = record
    { carrier    = List A
    ; _≈_        = _≡_
    ; _∼_        = _⊆_
    ; isPreorder = record
      { isEquivalence = PropEq.isEquivalence
      ; reflexive     = λ eq → PropEq.subst (_∈_ _) eq
      ; trans         = λ ys⊆zs xs⊆ys → xs⊆ys ∘ ys⊆zs
      ; ∼-resp-≈      = PropEq.resp₂ _⊆_
      }
    }

  module ⊆-Reasoning where
    import Relation.Binary.PreorderReasoning as PreR
    open PreR ⊆-preorder public
      renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _≈⟨_⟩_ to _≡⟨_⟩_)

    infix 1 _∈⟨_⟩_

    _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
    x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

------------------------------------------------------------------------
-- Another function

-- If any element satisfies P, then P is satisfied.

satisfied : ∀ {A} {P : A → Set} {xs} → Any P xs → ∃ P
satisfied = Prod.map id Prod.proj₂ ∘ Membership-≡.find
