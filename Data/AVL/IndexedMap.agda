------------------------------------------------------------------------
-- Finite maps with indexed keys and values, based on AVL trees
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product

module Data.AVL.IndexedMap
         {Index : Set} {Key : Index -> Set} {_≈_ _<_ : Rel (∃ Key)}
         (isOrderedKeySet : IsStrictTotalOrder _≈_ _<_)
         -- Equal keys must have equal indices.
         (indicesEqual : _≈_ =[ proj₁ ]⇒ _≡_)
         (Value : Index -> Set)
         where

open IsStrictTotalOrder isOrderedKeySet
import Data.AVL
open import Data.Function
open import Data.Maybe
open import Data.Bool
open import Data.List
open import Category.Functor
open RawFunctor MaybeFunctor

-- Key/value pairs.

KV : Set
KV = ∃ \i -> Key i × Value i

private

  -- Tree node contents. The value nothing is used to handle lookups
  -- and deletions; nothing is never stored in the tree.

  KMV : Set
  KMV = ∃ \i -> Key i × Maybe (Value i)

  fromKV : KV -> KMV
  fromKV (_ , k , v) = (_ , k , just v)

  toKV : KMV -> Maybe KV
  toKV (_ , k , nothing) = nothing  -- Impossible case.
  toKV (_ , k , just v)  = just (_ , k , v)

-- The order ignores the second component of the key/value pairs
-- completely.

Order : StrictTotalOrder
Order = record
  { carrier            = KMV
  ; _≈_                = _≈_ on₁ key
  ; _<_                = _<_ on₁ key
  ; isStrictTotalOrder = record
    { isEquivalence = record
      { refl  = Eq.refl
      ; sym   = Eq.sym
      ; trans = Eq.trans
      }
    ; trans         = trans
    ; compare       = cmp
    ; ≈-resp-<      = resp
    }
  }
  where
  key : KMV -> ∃ Key
  key (_ , k , _) = (, k)

  cmp : Trichotomous {KMV} (_≈_ on₁ key) (_<_ on₁ key)
  cmp (_ , k₁ , v₁) (_ , k₂ , v₂) with compare (, k₁) (, k₂)
  ... | tri< ≺ ≉ ≯ = tri< ≺ ≉ ≯
  ... | tri≈ ≮ ≋ ≯ = tri≈ ≮ ≋ ≯
  ... | tri> ≮ ≉ ≻ = tri> ≮ ≉ ≻

  resp : (_≈_ on₁ key) Respects₂ (_<_ on₁ key)
  resp = ((\{_ _ _} -> proj₁ ≈-resp-<) , (\{_ _ _} -> proj₂ ≈-resp-<))

-- The map type.

private module AVL = Data.AVL Order
open AVL public using () renaming (Tree to Map)

-- Repackaged functions.

empty : Map
empty = AVL.empty

singleton : forall {i} -> Key i -> Value i -> Map
singleton k v = AVL.singleton (_ , k , just v)

insert : forall {i} -> Key i -> Value i -> Map -> Map
insert k v = AVL.insert (_ , k , just v)

delete : forall {i} -> Key i -> Map -> Map
delete k = AVL.delete (_ , k , nothing)

lookup : forall {i} -> Key i -> Map -> Maybe (Value i)
lookup k m with AVL.lookup (_ , k , nothing) m
... | nothing                     = nothing
... | just ((i′ , k′ , mv′) , eq) with indicesEqual eq
...   | ≡-refl = mv′

_∈?_ : forall {i} -> Key i -> Map -> Bool
k ∈? m = AVL._∈?_ (_ , k , nothing) m

headTail : Map -> Maybe (KV × Map)
headTail m with AVL.headTail m
... | nothing         = nothing
... | just (kmv , m′) = (\kv -> kv , m′) <$> toKV kmv

initLast : Map -> Maybe (Map × KV)
initLast m with AVL.initLast m
... | nothing         = nothing
... | just (m′ , kmv) = _,_ m′ <$> toKV kmv

fromList : List KV -> Map
fromList = AVL.fromList ∘ map fromKV

toList : Map -> List KV
toList = gfilter toKV ∘ AVL.toList
