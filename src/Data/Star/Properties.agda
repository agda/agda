------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties related to Data.Star
------------------------------------------------------------------------

module Data.Star.Properties where

open import Data.Star
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; cong; cong₂)
import Relation.Binary.PreorderReasoning as PreR

------------------------------------------------------------------------
-- Equality

module _ {i t} {I : Set i} {T : Rel I t} {i j k} {x y : T i j} {xs ys} where

 ◅-injectiveˡ : (Star T i k ∋ x ◅ xs) ≡ y ◅ ys → x ≡ y
 ◅-injectiveˡ refl = refl

 ◅-injectiveʳ : (Star T i k ∋ x ◅ xs) ≡ y ◅ ys → xs ≡ ys
 ◅-injectiveʳ refl = refl

------------------------------------------------------------------------
-- Properties about combinators

◅◅-assoc : ∀ {i t} {I : Set i} {T : Rel I t} {i j k l}
           (xs : Star T i j) (ys : Star T j k)
           (zs : Star T k l) →
           (xs ◅◅ ys) ◅◅ zs ≡ xs ◅◅ (ys ◅◅ zs)
◅◅-assoc ε        ys zs = refl
◅◅-assoc (x ◅ xs) ys zs = cong (_◅_ x) (◅◅-assoc xs ys zs)

gmap-id : ∀ {i t} {I : Set i} {T : Rel I t} {i j} (xs : Star T i j) →
          gmap id id xs ≡ xs
gmap-id ε        = refl
gmap-id (x ◅ xs) = cong (_◅_ x) (gmap-id xs)

gmap-∘ : ∀ {i t} {I : Set i} {T : Rel I t}
           {j u} {J : Set j} {U : Rel J u}
           {k v} {K : Set k} {V : Rel K v}
         (f  : J → K) (g  : U =[ f  ]⇒ V)
         (f′ : I → J) (g′ : T =[ f′ ]⇒ U)
         {i j} (xs : Star T i j) →
         (gmap {U = V} f g ∘ gmap f′ g′) xs ≡ gmap (f ∘ f′) (g ∘ g′) xs
gmap-∘ f g f′ g′ ε        = refl
gmap-∘ f g f′ g′ (x ◅ xs) = cong (_◅_ (g (g′ x))) (gmap-∘ f g f′ g′ xs)

gmap-◅◅ : ∀ {i t j u}
            {I : Set i} {T : Rel I t} {J : Set j} {U : Rel J u}
          (f : I → J) (g : T =[ f ]⇒ U)
          {i j k} (xs : Star T i j) (ys : Star T j k) →
          gmap {U = U} f g (xs ◅◅ ys) ≡ gmap f g xs ◅◅ gmap f g ys
gmap-◅◅ f g ε        ys = refl
gmap-◅◅ f g (x ◅ xs) ys = cong (_◅_ (g x)) (gmap-◅◅ f g xs ys)

gmap-cong : ∀ {i t j u}
              {I : Set i} {T : Rel I t} {J : Set j} {U : Rel J u}
            (f : I → J) (g : T =[ f ]⇒ U) (g′ : T =[ f ]⇒ U) →
            (∀ {i j} (x : T i j) → g x ≡ g′ x) →
            ∀ {i j} (xs : Star T i j) →
            gmap {U = U} f g xs ≡ gmap f g′ xs
gmap-cong f g g′ eq ε        = refl
gmap-cong f g g′ eq (x ◅ xs) = cong₂ _◅_ (eq x) (gmap-cong f g g′ eq xs)

fold-◅◅ : ∀ {i p} {I : Set i}
          (P : Rel I p) (_⊕_ : Transitive P) (∅ : Reflexive P) →
          (∀ {i j} (x : P i j) → (∅ ⊕ x) ≡ x) →
          (∀ {i j k l} (x : P i j) (y : P j k) (z : P k l) →
             ((x ⊕ y) ⊕ z) ≡ (x ⊕ (y ⊕ z))) →
          ∀ {i j k} (xs : Star P i j) (ys : Star P j k) →
          fold P _⊕_ ∅ (xs ◅◅ ys) ≡ (fold P _⊕_ ∅ xs ⊕ fold P _⊕_ ∅ ys)
fold-◅◅ P _⊕_ ∅ left-unit assoc ε        ys = sym (left-unit _)
fold-◅◅ P _⊕_ ∅ left-unit assoc (x ◅ xs) ys = begin
  (x ⊕  fold P _⊕_ ∅ (xs ◅◅ ys))              ≡⟨ cong (_⊕_ x) $
                                                   fold-◅◅ P _⊕_ ∅ left-unit assoc xs ys ⟩
  (x ⊕ (fold P _⊕_ ∅ xs  ⊕ fold P _⊕_ ∅ ys))  ≡⟨ sym (assoc x _ _) ⟩
  ((x ⊕ fold P _⊕_ ∅ xs) ⊕ fold P _⊕_ ∅ ys)   ∎
  where open PropEq.≡-Reasoning

-- Reflexive transitive closures are preorders.

preorder : ∀ {i t} {I : Set i} (T : Rel I t) → Preorder _ _ _
preorder T = record
  { _≈_        = _≡_
  ; _∼_        = Star T
  ; isPreorder = record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive     = reflexive
    ; trans         = _◅◅_
    }
  }
  where
  reflexive : _≡_ ⇒ Star T
  reflexive refl = ε

-- Preorder reasoning for Star.

module StarReasoning {i t} {I : Set i} (T : Rel I t) where
  open PreR (preorder T) public
    renaming (_∼⟨_⟩_ to _⟶⋆⟨_⟩_; _≈⟨_⟩_ to _≡⟨_⟩_)

  infixr 2 _⟶⟨_⟩_

  _⟶⟨_⟩_ : ∀ x {y z} → T x y → y IsRelatedTo z → x IsRelatedTo z
  x ⟶⟨ x⟶y ⟩ y⟶⋆z = x ⟶⋆⟨ x⟶y ◅ ε ⟩ y⟶⋆z
