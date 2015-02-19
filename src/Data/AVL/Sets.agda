------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite sets, based on AVL trees
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

module Data.AVL.Sets
  {k ℓ} {Key : Set k} {_<_ : Rel Key ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

import Data.AVL as AVL
open import Data.Bool
open import Data.List.Base as List using (List)
open import Data.Maybe.Base as Maybe
open import Data.Product as Prod using (_×_; _,_; proj₁)
open import Data.Unit
open import Function
open import Level

-- The set type. (Note that Set is a reserved word.)

private
  open module S = AVL (const ⊤) isStrictTotalOrder
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

infix 4 _∈?_

_∈?_ : Key → ⟨Set⟩ → Bool
_∈?_ = S._∈?_

headTail : ⟨Set⟩ → Maybe (Key × ⟨Set⟩)
headTail s = Maybe.map (Prod.map proj₁ id) (S.headTail s)

initLast : ⟨Set⟩ → Maybe (⟨Set⟩ × Key)
initLast s = Maybe.map (Prod.map id proj₁) (S.initLast s)

fromList : List Key → ⟨Set⟩
fromList = S.fromList ∘ List.map (λ k → (k , _))

toList : ⟨Set⟩ → List Key
toList = List.map proj₁ ∘ S.toList
