------------------------------------------------------------------------
-- Finite sets, based on AVL trees
------------------------------------------------------------------------

open import Level
open import Relation.Binary

module Data.AVL.Sets
         (OrderedKeySet : StrictTotalOrder zero zero zero) where

import Data.AVL as AVL
open StrictTotalOrder OrderedKeySet renaming (Carrier to Key)
open import Data.Unit
open import Function
open import Data.Product as Prod using (_×_; _,_; proj₁)
open import Data.Maybe as Maybe
open import Data.Bool
open import Data.List as List using (List)
open import Category.Functor
open RawFunctor Maybe.functor

-- The set type. (Note that Set is a reserved word.)

private
  open module S = AVL OrderedKeySet (const ⊤)
    public using () renaming (Tree to ⟨Set⟩)

-- Repackaged functions.

empty : ⟨Set⟩
empty = S.empty

singleton : Key → ⟨Set⟩
singleton k = S.singleton k _

insert : Key → ⟨Set⟩ → ⟨Set⟩
insert k = S.insert k _

delete : Key → ⟨Set⟩ → ⟨Set⟩
delete = S.delete

lookup : Key → ⟨Set⟩ → Maybe Key
lookup k s = proj₁ <$> S.lookup k s

_∈?_ : Key → ⟨Set⟩ → Bool
_∈?_ = S._∈?_

headTail : ⟨Set⟩ → Maybe (Key × ⟨Set⟩)
headTail s = Prod.map proj₁ id <$> S.headTail s

initLast : ⟨Set⟩ → Maybe (⟨Set⟩ × Key)
initLast s = Prod.map id proj₁ <$> S.initLast s

fromList : List Key → ⟨Set⟩
fromList = S.fromList ∘ List.map (λ k → (k , _))

toList : ⟨Set⟩ → List Key
toList = List.map proj₁ ∘ S.toList
