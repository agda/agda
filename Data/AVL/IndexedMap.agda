------------------------------------------------------------------------
-- Finite maps with indexed keys and values, based on AVL trees
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product as Prod hiding (map)

module Data.AVL.IndexedMap
         {Index : Set} {Key : Index → Set} {_≈_ _<_ : Rel (∃ Key)}
         (isOrderedKeySet : IsStrictTotalOrder _≈_ _<_)
         -- Equal keys must have equal indices.
         (indicesEqual : _≈_ =[ proj₁ ]⇒ _≡_)
         (Value : Index → Set)
         where

import Data.AVL
open import Data.Function
open import Data.Maybe as Maybe
open import Data.Bool
open import Data.List
open import Category.Functor
open RawFunctor Maybe.functor

-- Key/value pairs.

KV : Set
KV = ∃ λ i → Key i × Value i

-- Conversions.

private

  fromKV : KV → Σ (∃ Key) λ ik → Value (proj₁ ik)
  fromKV (i , k , v) = ((i , k) , v)

  toKV : Σ (∃ Key) (λ ik → Value (proj₁ ik)) → KV
  toKV ((i , k) , v) = (i , k , v)

private

  Order : StrictTotalOrder
  Order = record { isStrictTotalOrder = isOrderedKeySet }

-- The map type.

private
  open module AVL = Data.AVL Order (λ ik → Value (proj₁ ik))
    public using () renaming (Tree to Map)

-- Repackaged functions.

empty : Map
empty = AVL.empty

singleton : ∀ {i} → Key i → Value i → Map
singleton k v = AVL.singleton (, k) v

insert : ∀ {i} → Key i → Value i → Map → Map
insert k v = AVL.insert (, k) v

delete : ∀ {i} → Key i → Map → Map
delete k = AVL.delete (, k)

lookup : ∀ {i} → Key i → Map → Maybe (Value i)
lookup k m with AVL.lookup (_ , k) m
... | nothing                    = nothing
... | just ((i′ , k′) , v′ , eq) with indicesEqual eq
...   | refl = just v′

_∈?_ : ∀ {i} → Key i → Map → Bool
_∈?_ k = AVL._∈?_ (, k)

headTail : Map → Maybe (KV × Map)
headTail m = Prod.map toKV id <$> AVL.headTail m

initLast : Map → Maybe (Map × KV)
initLast m = Prod.map id toKV <$> AVL.initLast m

fromList : List KV → Map
fromList = AVL.fromList ∘ map fromKV

toList : Map → List KV
toList = map toKV ∘ AVL.toList
