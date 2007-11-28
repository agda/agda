------------------------------------------------------------------------
-- Finite maps (i.e. lookup tables)
------------------------------------------------------------------------

module Data.Map where

open import Relation.Nullary
open import Relation.Binary
open import Logic
open import Data.List hiding (map)
open import Data.Product

module Map₁ (key-dto : DecTotalOrder) (elem-s : Setoid) where

  private
    open module DTO = DecTotalOrderOps key-dto
    open module P   = Poset poset
      renaming (carrier to key)
    open module S   = SetoidOps elem-s
      renaming (carrier to elem; _≈_ to _≗_)

  infixr 6 _∪_
  infix  5 _∈?_
  infix  4 _∈_ _|≈|_

  abstract postulate Map-decSetoid : DecSetoid

  Map : Set
  Map = SetoidOps.carrier (DecSetoidOps.setoid Map-decSetoid)

  _|≈|_ : Rel Map
  _|≈|_ = SetoidOps._≈_ (DecSetoidOps.setoid Map-decSetoid)

  abstract
   postulate
    empty  : Map
    insert : key -> elem -> Map -> Map
    _∪_    : Map -> Map -> Map
    _∈_    : key -> Map -> Set
    _↦_∈_  : key -> elem -> Map -> Set

  data LookupResult (k : key) (s : Map) : Set where
    found    : (e : elem) -> k ↦ e ∈ s -> LookupResult k s
    notFound : ¬ k ∈ s -> LookupResult k s

  abstract
   postulate
    _∈?_   : (k : key) -> (s : Map) -> LookupResult k s
    toList : Map -> [ key × elem ]

   postulate
    prop-∈₁ : forall {x v s}   -> x ↦ v ∈ s -> x ∈ s
    prop-∈₂ : forall {x s}     -> x ∈ s -> ∃ elem (\v -> x ↦ v ∈ s)
    prop-∈₃ : forall {x v w s} -> x ↦ v ∈ s -> x ↦ w ∈ s -> v ≗ w

    prop-∈-insert₁ :  forall {x y v w s}
                   -> x ≈ y -> v ≗ w -> x ↦ v ∈ insert y w s
    prop-∈-insert₂ :  forall {x y v w s}
                   -> ¬ x ≈ y -> x ↦ v ∈ s -> x ↦ v ∈ insert y w s
    prop-∈-insert₃ :  forall {x y v w s}
                   -> ¬ x ≈ y -> x ↦ v ∈ insert y w s -> x ↦ v ∈ s

    prop-∈-empty : forall {x} -> ¬ x ∈ empty

    prop-∈-∪ : forall {x s₁ s₂} -> x ∈ s₁ -> x ∈ s₁ ∪ s₂

    prop-∪₁ : forall {s₁ s₂}    -> s₁ ∪ s₂        |≈| s₂ ∪ s₁
    prop-∪₂ : forall {s₁ s₂ s₃} -> s₁ ∪ (s₂ ∪ s₃) |≈| (s₁ ∪ s₂) ∪ s₃

    prop-∈-|≈|₁ : forall {x}   -> _|≈|_ Respects (\s -> x ∈ s)
    prop-∈-|≈|₂ : forall {x v} -> _|≈|_ Respects (\s -> x ↦ v ∈ s)
    prop-∈-≈₁   : forall {s}   -> _≈_   Respects (\x -> x ∈ s)
    prop-∈-≈₂   : forall {v s} -> _≈_   Respects (\x -> x ↦ v ∈ s)
    prop-∈-≗    : forall {x s} -> _≗_   Respects (\v -> x ↦ v ∈ s)

    -- TODO: Postulates for toList.

  singleton : key -> elem -> Map
  singleton k v = insert k v empty

  ⋃_ : [ Map ] -> Map
  ⋃_ = foldr _∪_ empty

  fromList : [ key × elem ] -> Map
  fromList = foldr (uncurry insert) empty

open Map₁ public renaming (Map to _⇰_)
