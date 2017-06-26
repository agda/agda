------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed containers aka interaction structures aka polynomial
-- functors. The notation and presentation here is closest to that of
-- Hancock and Hyvernat in "Programming interfaces and basic topology"
-- (2006/9).
--
------------------------------------------------------------------------

module Data.Container.Indexed where

open import Level
open import Function renaming (id to ⟨id⟩; _∘_ to _⟨∘⟩_)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (_↔_; module Inverse)
open import Data.Product as Prod hiding (map)
open import Relation.Unary using (Pred; _⊆_)
open import Relation.Binary as B using (Preorder; module Preorder)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
open import Relation.Binary.Indexed
open import Data.W.Indexed
open import Data.M.Indexed

------------------------------------------------------------------------

-- The type and its semantics ("extension").

open import Data.Container.Indexed.Core public
open Container public

-- Abbreviation for the commonly used level one version of indexed
-- containers.

_▷_ : Set → Set → Set₁
I ▷ O = Container I O zero zero

-- The least and greatest fixpoint.

μ ν : ∀ {o c r} {O : Set o} → Container O O c r → Pred O _
μ = W
ν = M

-- Equality, parametrised on an underlying relation.

Eq : ∀ {i o c r ℓ} {I : Set i} {O : Set o} (C : Container I O c r)
     (X Y : Pred I ℓ) → REL X Y ℓ → REL (⟦ C ⟧ X) (⟦ C ⟧ Y) _
Eq C _ _ _≈_ {o₁} {o₂} (c , k) (c′ , k′) =
  o₁ ≡ o₂ × c ≅ c′ × (∀ r r′ → r ≅ r′ → k r ≈ k′ r′)

private

  -- Note that, if propositional equality were extensional, then Eq _≅_
  -- and _≅_ would coincide.

  Eq⇒≅ : ∀ {i o c r ℓ} {I : Set i} {O : Set o}
         {C : Container I O c r} {X : Pred I ℓ} {o₁ o₂ : O}
         {xs : ⟦ C ⟧ X o₁} {ys : ⟦ C ⟧ X o₂} → H.Extensionality r ℓ →
         Eq C X X (λ x₁ x₂ → x₁ ≅ x₂) xs ys → xs ≅ ys
  Eq⇒≅ {xs = c , k} {.c , k′} ext (refl , refl , k≈k′) =
    H.cong (_,_ c) (ext (λ _ → refl) (λ r → k≈k′ r r refl))

setoid : ∀ {i o c r s} {I : Set i} {O : Set o} →
         Container I O c r → Setoid I s _ → Setoid O _ _
setoid C X = record
  { Carrier       = ⟦ C ⟧ X.Carrier
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl , refl , λ { r .r refl → X.refl }
    ; sym   = sym
    ; trans = λ { {_} {i = xs} {ys} {zs} → trans {_} {i = xs} {ys} {zs}  }
    }
  }
  where
  module X = Setoid X

  _≈_ : Rel (⟦ C ⟧ X.Carrier) _
  _≈_ = Eq C X.Carrier X.Carrier X._≈_

  sym : Symmetric (⟦ C ⟧ X.Carrier) _≈_
  sym {_} {._} {_ , _} {._ , _} (refl , refl , k) =
    refl , refl , λ { r .r refl → X.sym (k r r refl) }

  trans : Transitive (⟦ C ⟧ X.Carrier) _≈_
  trans {._} {_} {._} {_ , _} {._ , _} {._ , _}
    (refl , refl , k) (refl , refl , k′) =
      refl , refl , λ { r .r refl → X.trans (k r r refl) (k′ r r refl) }

------------------------------------------------------------------------
-- Functoriality

-- Indexed containers are functors.

map : ∀ {i o c r ℓ₁ ℓ₂} {I : Set i} {O : Set o}
      (C : Container I O c r) {X : Pred I ℓ₁} {Y : Pred I ℓ₂} →
      X ⊆ Y → ⟦ C ⟧ X ⊆ ⟦ C ⟧ Y
map _ f = Prod.map ⟨id⟩ (λ g → f ⟨∘⟩ g)

module Map where

  identity : ∀ {i o c r s} {I : Set i} {O : Set o} (C : Container I O c r)
             (X : Setoid I s _) → let module X = Setoid X in
             ∀ {o} {xs : ⟦ C ⟧ X.Carrier o} → Eq C X.Carrier X.Carrier
             X._≈_ xs (map C {X.Carrier} ⟨id⟩ xs)
  identity C X = Setoid.refl (setoid C X)

  composition : ∀ {i o c r s ℓ₁ ℓ₂} {I : Set i} {O : Set o}
                (C : Container I O c r) {X : Pred I ℓ₁} {Y : Pred I ℓ₂}
                (Z : Setoid I s _) → let module Z = Setoid Z in
                {f : Y ⊆ Z.Carrier} {g : X ⊆ Y} {o : O} {xs : ⟦ C ⟧ X o} →
                Eq C Z.Carrier Z.Carrier Z._≈_
                  (map C {Y} f (map C {X} g xs))
                  (map C {X} (f ⟨∘⟩ g) xs)
  composition C Z = Setoid.refl (setoid C Z)

------------------------------------------------------------------------
-- Container morphisms

module _ {i₁ i₂ o₁ o₂}
         {I₁ : Set i₁} {I₂ : Set i₂} {O₁ : Set o₁} {O₂ : Set o₂} where

  -- General container morphism.

  record ContainerMorphism {c₁ c₂ r₁ r₂ ℓ₁ ℓ₂}
         (C₁ : Container I₁ O₁ c₁ r₁) (C₂ : Container I₂ O₂ c₂ r₂)
         (f : I₁ → I₂) (g : O₁ → O₂)
         (_∼_ : B.Rel I₂ ℓ₁) (_≈_ : B.REL (Set r₂) (Set r₁) ℓ₂)
         (_·_ : ∀ {A B} → A ≈ B → A → B) :
         Set (i₁ ⊔ i₂ ⊔ o₁ ⊔ o₂ ⊔ c₁ ⊔ c₂ ⊔ r₁ ⊔ r₂ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      command   : Command C₁ ⊆ Command C₂ ⟨∘⟩ g
      response  : ∀ {o} {c₁ : Command C₁ o} →
                  Response C₂ (command c₁) ≈ Response C₁ c₁
      coherent  : ∀ {o} {c₁ : Command C₁ o} {r₂ : Response C₂ (command c₁)} →
                  f (next C₁ c₁ (response · r₂)) ∼ next C₂ (command c₁) r₂

  open ContainerMorphism public

  -- Plain container morphism.

  _⇒[_/_]_ : ∀ {c₁ c₂ r₁ r₂} →
             Container I₁ O₁ c₁ r₁ → (I₁ → I₂) → (O₁ → O₂) →
             Container I₂ O₂ c₂ r₂ → Set _
  C₁ ⇒[ f / g ] C₂ = ContainerMorphism C₁ C₂ f g _≡_ (λ R₂ R₁ → R₂ → R₁) _$_

  -- Linear container morphism.

  _⊸[_/_]_ : ∀ {c₁ c₂ r₁ r₂} →
             Container I₁ O₁ c₁ r₁ → (I₁ → I₂) → (O₁ → O₂) →
             Container I₂ O₂ c₂ r₂ → Set _
  C₁ ⊸[ f / g ] C₂ = ContainerMorphism C₁ C₂ f g _≡_ _↔_
                                       (λ r₂↔r₁ r₂ → Inverse.to r₂↔r₁ ⟨$⟩ r₂)

  -- Cartesian container morphism.

  _⇒C[_/_]_ : ∀ {c₁ c₂ r} →
              Container I₁ O₁ c₁ r → (I₁ → I₂) → (O₁ → O₂) →
              Container I₂ O₂ c₂ r → Set _
  C₁ ⇒C[ f / g ] C₂ = ContainerMorphism C₁ C₂ f g _≡_ (λ R₂ R₁ → R₂ ≡ R₁)
                                        (λ r₂≡r₁ r₂ → P.subst ⟨id⟩ r₂≡r₁ r₂)

-- Degenerate cases where no reindexing is performed.

module _ {i o c r} {I : Set i} {O : Set o} where

  _⇒_ : B.Rel (Container I O c r) _
  C₁ ⇒ C₂ = C₁ ⇒[ ⟨id⟩ / ⟨id⟩ ] C₂

  _⊸_ : B.Rel (Container I O c r) _
  C₁ ⊸ C₂ = C₁ ⊸[ ⟨id⟩ / ⟨id⟩ ] C₂

  _⇒C_ : B.Rel (Container I O c r) _
  C₁ ⇒C C₂ = C₁ ⇒C[ ⟨id⟩ / ⟨id⟩ ] C₂

------------------------------------------------------------------------
-- Plain morphisms

-- Interpretation of _⇒_.

⟪_⟫ : ∀ {i o c r ℓ} {I : Set i} {O : Set o} {C₁ C₂ : Container I O c r} →
      C₁ ⇒ C₂ → (X : Pred I ℓ) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X
⟪ m ⟫ X (c , k) = command m c , λ r₂ →
  P.subst X (coherent m) (k (response m r₂))

module PlainMorphism {i o c r} {I : Set i} {O : Set o} where

  -- Naturality.

  Natural : ∀ {ℓ} {C₁ C₂ : Container I O c r} →
            ((X : Pred I ℓ) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X) → Set _
  Natural {C₁ = C₁} {C₂} m =
    ∀ {X} Y → let module Y = Setoid Y in (f : X ⊆ Y.Carrier) →
    ∀ {o} (xs : ⟦ C₁ ⟧ X o) →
      Eq C₂ Y.Carrier Y.Carrier Y._≈_
        (m Y.Carrier $ map C₁ {X} f xs) (map C₂ {X} f $ m X xs)

  -- Natural transformations.

  NT : ∀ {ℓ} (C₁ C₂ : Container I O c r) → Set _
  NT {ℓ} C₁ C₂ = ∃ λ (m : (X : Pred I ℓ) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X) →
                 Natural m

  -- Container morphisms are natural.

  natural : ∀ {ℓ} (C₁ C₂ : Container I O c r) (m : C₁ ⇒ C₂) → Natural {ℓ} ⟪ m ⟫
  natural _ _ m {X} Y f _ = refl , refl , λ { r .r refl → lemma (coherent m) }
    where
    module Y = Setoid Y

    lemma : ∀ {i j} (eq : i ≡ j) {x} →
            P.subst Y.Carrier eq (f x) Y.≈ f (P.subst X eq x)
    lemma refl = Y.refl

  -- In fact, all natural functions of the right type are container
  -- morphisms.

  complete : ∀ {C₁ C₂ : Container I O c r} (nt : NT C₁ C₂) →
             ∃ λ m → (X : Setoid I _ _) →
                     let module X = Setoid X in
                     ∀ {o} (xs : ⟦ C₁ ⟧ X.Carrier o) →
                     Eq C₂ X.Carrier X.Carrier X._≈_
                       (proj₁ nt X.Carrier xs) (⟪ m ⟫ X.Carrier {o} xs)
  complete {C₁} {C₂} (nt , nat) = m , (λ X xs → nat X
    (λ { (r , eq) → P.subst (Setoid.Carrier X) eq (proj₂ xs r) })
    (proj₁ xs , (λ r → r , refl)))
    where

    m : C₁ ⇒ C₂
    m = record
      { command  = λ      c₁       → proj₁        (lemma c₁)
      ; response = λ {_} {c₁}  r₂  → proj₁ (proj₂ (lemma c₁) r₂)
      ; coherent = λ {_} {c₁} {r₂} → proj₂ (proj₂ (lemma c₁) r₂)
      }
      where
      lemma : ∀ {o} (c₁ : Command C₁ o) → Σ[ c₂ ∈ Command C₂ o ]
              ((r₂ : Response C₂ c₂) → Σ[ r₁ ∈ Response C₁ c₁ ]
              next C₁ c₁ r₁ ≡ next C₂ c₂ r₂)
      lemma c₁ = nt (λ i → Σ[ r₁ ∈ Response C₁ c₁ ] next C₁ c₁ r₁ ≡ i)
                    (c₁ , λ r₁ → r₁ , refl)

  -- Identity.

  id : (C : Container I O c r) → C ⇒ C
  id _ = record
    { command  = ⟨id⟩
    ; response = ⟨id⟩
    ; coherent = refl
    }

  -- Composition.

  infixr 9 _∘_

  _∘_ : {C₁ C₂ C₃ : Container I O c r} →
        C₂ ⇒ C₃ → C₁ ⇒ C₂ → C₁ ⇒ C₃
  f ∘ g = record
    { command  = command  f ⟨∘⟩ command g
    ; response = response g ⟨∘⟩ response f
    ; coherent = coherent g ⟨ P.trans ⟩ coherent f
    }

  -- Identity and composition commute with ⟪_⟫.

  id-correct : ∀ {ℓ} {C : Container I O c r} → ∀ {X : Pred I ℓ} {o} →
               ⟪ id C ⟫ X {o} ≗ ⟨id⟩
  id-correct _ = refl

  ∘-correct : {C₁ C₂ C₃ : Container I O c r}
              (f : C₂ ⇒ C₃) (g : C₁ ⇒ C₂) (X : Setoid I (c ⊔ r) _) →
              let module X = Setoid X in
              ∀ {o} {xs : ⟦ C₁ ⟧ X.Carrier o} →
              Eq C₃ X.Carrier X.Carrier X._≈_
                (⟪ f ∘ g ⟫ X.Carrier xs)
                (⟪ f ⟫ X.Carrier (⟪ g ⟫ X.Carrier xs))
  ∘-correct f g X = refl , refl , λ { r .r refl → lemma (coherent g)
                                                        (coherent f) }
    where
    module X = Setoid X

    lemma : ∀ {i j k} (eq₁ : i ≡ j) (eq₂ : j ≡ k) {x} →
      P.subst X.Carrier (P.trans eq₁ eq₂) x
      X.≈
      P.subst X.Carrier eq₂ (P.subst X.Carrier eq₁ x)
    lemma refl refl = X.refl

------------------------------------------------------------------------
-- Linear container morphisms

module LinearMorphism
  {i o c r} {I : Set i} {O : Set o} {C₁ C₂ : Container I O c r}
  (m : C₁ ⊸ C₂)
  where

  morphism : C₁ ⇒ C₂
  morphism = record
    { command  = command m
    ; response = _⟨$⟩_ (Inverse.to (response m))
    ; coherent = coherent m
    }

  ⟪_⟫⊸ : ∀ {ℓ} (X : Pred I ℓ) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X
  ⟪_⟫⊸ = ⟪ morphism ⟫

open LinearMorphism public using (⟪_⟫⊸)

------------------------------------------------------------------------
-- Cartesian morphisms

module CartesianMorphism
  {i o c r} {I : Set i} {O : Set o} {C₁ C₂ : Container I O c r}
  (m : C₁ ⇒C C₂)
  where

  morphism : C₁ ⇒ C₂
  morphism = record
    { command  = command m
    ; response = P.subst ⟨id⟩ (response m)
    ; coherent = coherent m
    }

  ⟪_⟫C : ∀ {ℓ} (X : Pred I ℓ) → ⟦ C₁ ⟧ X ⊆ ⟦ C₂ ⟧ X
  ⟪_⟫C = ⟪ morphism ⟫

open CartesianMorphism public using (⟪_⟫C)

------------------------------------------------------------------------
-- All and any

-- □ and ◇ are defined in the core module.

module _ {i o c r ℓ₁ ℓ₂} {I : Set i} {O : Set o} (C : Container I O c r)
         {X : Pred I ℓ₁} {P Q : Pred (Σ I X) ℓ₂} where

  -- All.

  □-map : P ⊆ Q → □ C P ⊆ □ C Q
  □-map P⊆Q = _⟨∘⟩_ P⊆Q

  -- Any.

  ◇-map : P ⊆ Q → ◇ C P ⊆ ◇ C Q
  ◇-map P⊆Q = Prod.map ⟨id⟩ P⊆Q

-- Membership.

infix 4 _∈_

_∈_ : ∀ {i o c r ℓ} {I : Set i} {O : Set o}
      {C : Container I O c r} {X : Pred I (i ⊔ ℓ)} → REL X (⟦ C ⟧ X) _
_∈_ {C = C} {X} x xs = ◇ C {X = X} (_≅_ x) (, xs)
