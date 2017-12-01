------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees
------------------------------------------------------------------------

-- AVL trees are balanced binary search trees.

-- The search tree invariant is specified using the technique
-- described by Conor McBride in his talk "Pivotal pragmatism".

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_ ; refl)

module Data.AVL
  {k r} {Key : Set k} {_<_ : Rel Key r}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

open import Data.Bool.Base using (Bool)
import Data.DifferenceList as DiffList
open import Data.Empty
open import Data.List.Base as List using (List)
open import Data.Maybe.Base hiding (map)
open import Data.Nat.Base hiding (_<_; _⊔_; compare)
open import Data.Product hiding (map)
open import Data.Unit
open import Function
open import Level using (_⊔_; Lift; lift)

open IsStrictTotalOrder isStrictTotalOrder
import Data.AVL.Indexed Key isStrictTotalOrder as Indexed
open Indexed using (K&_ ; ⊥⁺ ; ⊤⁺)

------------------------------------------------------------------------
-- Types and functions with hidden indices

data Tree {v} (V : Key → Set v) : Set (k ⊔ v ⊔ r) where
  tree : ∀ {h} → Indexed.Tree V ⊥⁺ ⊤⁺ h → Tree V

module _ {v} {V : Key → Set v} where

  empty : Tree V
  empty = tree (Indexed.empty _)

  singleton : (k : Key) → V k → Tree V
  singleton k v = tree (Indexed.singleton k v _)

  insert : (k : Key) → V k → Tree V → Tree V
  insert k v (tree t) = tree $ proj₂ $ Indexed.insert k v t _

  insertWith : (k : Key) → V k → (V k → V k → V k) →
               Tree V → Tree V
  insertWith k v f (tree t) = tree $ proj₂ $ Indexed.insertWith k v f t _

  delete : Key → Tree V → Tree V
  delete k (tree t) = tree $ proj₂ $ Indexed.delete k t

  lookup : (k : Key) → Tree V → Maybe (V k)
  lookup k (tree t) = Indexed.lookup k t

module _ {v w} {V : Key → Set v} {W : Key → Set w} where

  map : ({k : Key} → V k → W k) → Tree V → Tree W
  map f (tree t) = tree $ Indexed.map f t

module _ {v} {V : Key → Set v} where

  infix 4 _∈?_

  _∈?_ : Key → Tree V → Bool
  k ∈? t = is-just (lookup k t)

  headTail : Tree V → Maybe ((K& V) × Tree V)
  headTail (tree (Indexed.leaf _)) = nothing
  headTail (tree {h = suc _} t)    with Indexed.headTail t
  ... | (k , _ , _ , t′) = just (k , tree (Indexed.castˡ _ t′))

  initLast : Tree V → Maybe (Tree V × (K& V))
  initLast (tree (Indexed.leaf _)) = nothing
  initLast (tree {h = suc _} t)    with Indexed.initLast t
  ... | (k , _ , _ , t′) = just (tree (Indexed.castʳ t′ _) , k)

  -- The input does not need to be ordered.

  fromList : List (K& V) → Tree V
  fromList = List.foldr (uncurry insert) empty

  -- Returns an ordered list.

  toList : Tree V → List (K& V)
  toList (tree t) = DiffList.toList (Indexed.toDiffList t)

  -- Naive implementations of union.

  unionWith : (∀ {k} → V k → V k → V k) →
              -- Left → right → result.
              Tree V → Tree V → Tree V
  unionWith f t₁ t₂ =
    List.foldr (λ { (k , v) → insertWith k v f }) t₂ (toList t₁)

  -- Left-biased.

  union : Tree V → Tree V → Tree V
  union = unionWith const

  unionsWith : (∀ {k} → V k → V k → V k) → List (Tree V) → Tree V
  unionsWith f ts = List.foldr (unionWith f) empty ts

  -- Left-biased.

  unions : List (Tree V) → Tree V
  unions = unionsWith const
