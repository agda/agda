------------------------------------------------------------------------
-- Finite sets
------------------------------------------------------------------------

module Data.Sets where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.OrderMorphism
open import Logic
open import Data.Function
open import Data.List hiding (map)
open import Data.Product

module Sets₁ (dto : DecTotalOrder) where

  open DecTotalOrder dto public using (_≈_)
  open DecTotalOrder dto hiding (_≈_)

  infixr 6 _∪_
  infix  5 _∈?_
  infix  4 _∈_ _|≈|_

  abstract postulate Set-decSetoid : DecSetoid

  <Set> : Set
  <Set> = DecSetoid.carrier Set-decSetoid

  _|≈|_ : Rel <Set>
  _|≈|_ = DecSetoid._≈_ Set-decSetoid

  abstract
   postulate
    empty  : <Set>
    insert : carrier -> <Set> -> <Set>
    _∪_    : <Set> -> <Set> -> <Set>
    _∈_    : carrier -> <Set> -> Set
    _∈?_   : (x : carrier) -> (s : <Set>) -> Dec (x ∈ s)
    toList : <Set> -> [ carrier ]

   postulate
    prop-∈-insert₁ :  forall {x y s} -> x ≈ y -> x ∈ insert y s
    prop-∈-insert₂ :  forall {x y s} -> x ∈ s -> x ∈ insert y s
    prop-∈-insert₃ :  forall {x y s}
                   -> ¬ x ≈ y -> x ∈ insert y s -> x ∈ s

    prop-∈-empty : forall {x} -> ¬ x ∈ empty

    prop-∈-∪ : forall {x s₁ s₂} -> x ∈ s₁ -> x ∈ s₁ ∪ s₂

    prop-∪₁ : forall {s₁ s₂}    -> s₁ ∪ s₂        |≈| s₂ ∪ s₁
    prop-∪₂ : forall {s₁ s₂ s₃} -> s₁ ∪ (s₂ ∪ s₃) |≈| (s₁ ∪ s₂) ∪ s₃

    prop-∈-|≈| : forall {x} -> _|≈|_ Respects (\s -> x ∈ s)
    prop-∈-≈   : forall {s} -> _≈_   Respects (\x -> x ∈ s)

    -- TODO: Postulates for toList.

  singleton : carrier -> <Set>
  singleton x = insert x empty

  ⋃_ : [ <Set> ] -> <Set>
  ⋃_ = foldr _∪_ empty

  fromList : [ carrier ] -> <Set>
  fromList = foldr insert empty

  _⊆_ : <Set> -> <Set> -> Set
  s₁ ⊆ s₂ = forall x -> x ∈ s₁ -> x ∈ s₂

open Sets₁ public
open DecTotalOrder hiding (_≈_)
open _⇒_

abstract
 postulate
  map : forall {do₁ do₂} -> do₁ ⇒-DTO do₂ -> <Set> do₁ -> <Set> do₂
  mapToSet
    :  forall {do₁ do₂}
    -> (carrier do₁ -> <Set> do₂)
    -> <Set> do₁ -> <Set> do₂

  prop-map-∈₁
    :  forall {do₁ do₂ f x s}
    ->       x ⟨ _∈_ do₁ ⟩₁       s
    -> fun f x ⟨ _∈_ do₂ ⟩₁ map f s
  prop-map-∈₂
    :  forall {do₁ do₂ f y s}
    -> y ⟨ _∈_ do₂ ⟩₁ map f s
    -> ∃ _ (\x -> (fun f x ⟨ _≈_ do₂ ⟩₁ y) ×
                  (      x ⟨ _∈_ do₁ ⟩₁ s))

  prop-mapToSet₁
    :  forall {do₁ do₂ f x s}
    ->   x ⟨ _∈_ do₁ ⟩₁            s
    -> f x ⟨ _⊆_ do₂ ⟩₁ mapToSet f s
  prop-mapToSet₂
    :  forall {do₁ do₂ f y s}
    -> y ⟨ _∈_ do₂ ⟩₁ mapToSet f s
    -> ∃ _ (\x -> (y ⟨ _∈_ do₂ ⟩₁ f x) ×
                  (x ⟨ _∈_ do₁ ⟩₁ s))
