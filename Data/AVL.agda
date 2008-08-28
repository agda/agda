------------------------------------------------------------------------
-- AVL trees
------------------------------------------------------------------------

-- AVL trees are balanced binary search trees. The search tree
-- invariant is not statically enforced in the current implementation,
-- just the balance invariant.

-- There are no "values" in the trees, just keys. Key/value pairs can
-- be handled by defining an equality/ordering relation which ignores
-- the second component.

open import Relation.Binary

module Data.AVL (OrderedKeySet : StrictTotalOrder) where

open import Data.Nat hiding (compare)
open StrictTotalOrder OrderedKeySet renaming (carrier to Key)
open import Data.Product
open import Data.Maybe
import Data.List as List
open List using (List)
import Data.DifferenceList as DiffList
open import Data.Function

------------------------------------------------------------------------
-- Types and functions which are used to keep track of invariants

module Invariants where

  infix 4 _∼_ _≲_

  -- If m ∼ n, then the difference between m and n is at most 1. _∼_
  -- is used to record the balance factor of the AVL trees, and also
  -- to ensure that the absolute value of the balance factor is never
  -- more than 1.

  data _∼_ : ℕ -> ℕ -> Set where
    ∼+ : forall {n} ->     n ∼ 1 + n
    ∼0 : forall {n} ->     n ∼ n
    ∼- : forall {n} -> 1 + n ∼ n

  -- If m ≲ n, then m ∼ n and m ≤ n.

  data _≲_ : ℕ -> ℕ -> Set where
    ∼+ : forall {n} -> n ≲ 1 + n
    ∼0 : forall {n} -> n ≲ n

  -- The maximum of m and n.

  max : forall {m n} -> m ∼ n -> ℕ
  max (∼+ {n}) = 1 + n
  max (∼0 {n}) =     n
  max (∼- {n}) = 1 + n

  -- Some lemmas.

  1+ : forall {m n} -> m ∼ n -> 1 + m ∼ 1 + n
  1+ ∼+ = ∼+
  1+ ∼0 = ∼0
  1+ ∼- = ∼-

  max∼ : forall {i j} (bal : i ∼ j) -> max bal ∼ i
  max∼ ∼+ = ∼-
  max∼ ∼0 = ∼0
  max∼ ∼- = ∼0

  ∼max : forall {i j} (bal : i ∼ j) -> j ∼ max bal
  ∼max ∼+ = ∼0
  ∼max ∼0 = ∼0
  ∼max ∼- = ∼+

  max∼max : forall {i j} (bal : i ∼ j) ->
            max (max∼ bal) ∼ max (∼max bal)
  max∼max ∼+ = ∼0
  max∼max ∼0 = ∼0
  max∼max ∼- = ∼0

  max-lemma : forall {m n} (bal : m ∼ n) ->
              max (1+ (max∼max bal)) ≲ 2 + max bal
  max-lemma ∼+ = ∼+
  max-lemma ∼0 = ∼+
  max-lemma ∼- = ∼+

------------------------------------------------------------------------
-- AVL trees

module Indexed where

  open Invariants

  -- The trees are indexed on their height.

  data Tree : ℕ -> Set where
    leaf : Tree 0
    node : forall {h₁ h₂}
           (bal : h₁ ∼ h₂)  -- Balance factor.
           (l : Tree h₁) (k : Key) (r : Tree h₂) ->
           Tree (1 + max bal)

  -- An empty tree.

  empty : Tree 0
  empty = leaf

  -- A singleton tree.

  singleton : Key -> Tree 1
  singleton k = node ∼0 leaf k leaf

  -- joinˡ _ l k r returns a tree containing l before k before r.

  joinˡ : forall {hˡ hʳ} (bal : hˡ ∼ hʳ) ->
          ∃ (\h -> Tree (1 + h) × h ≲ hˡ) ->
          Key -> Tree hʳ ->
          ∃ (\h -> Tree (1 + h) × h ≲ 1 + max bal)
  joinˡ ∼- (._ , node ∼- t₁ k₂ t₃ , ∼0) k₄ t₅ = (_ , node ∼0 t₁ k₂ (node ∼0 t₃ k₄ t₅) , ∼+)
  joinˡ ∼- (._ , node ∼0 t₁ k₂ t₃ , ∼0) k₄ t₅ = (_ , node ∼+ t₁ k₂ (node ∼- t₃ k₄ t₅) , ∼0)
  joinˡ ∼- (._ , node ∼+ t₁ k₂
                   (node bal t₃ k₄ t₅)
                                  , ∼0) k₆ t₇ = (_ , node (1+ (max∼max bal))
                                                       (node (max∼ bal) t₁ k₂ t₃)
                                                       k₄
                                                       (node (∼max bal) t₅ k₆ t₇)
                                                   , max-lemma bal)
  joinˡ ∼- (._ , t₁ , ∼+) k₂ t₃ = (_ , node ∼- t₁ k₂ t₃ , ∼+)
  joinˡ ∼0 (_  , t₁ , ∼0) k₂ t₃ = (_ , node ∼- t₁ k₂ t₃ , ∼0)
  joinˡ ∼0 (_  , t₁ , ∼+) k₂ t₃ = (_ , node ∼0 t₁ k₂ t₃ , ∼+)
  joinˡ ∼+ (_  , t₁ , ∼0) k₂ t₃ = (_ , node ∼0 t₁ k₂ t₃ , ∼+)
  joinˡ ∼+ (_  , t₁ , ∼+) k₂ t₃ = (_ , node ∼+ t₁ k₂ t₃ , ∼+)

  -- joinʳ _ l k r also returns a tree containing l before k before r.

  joinʳ : forall {hˡ hʳ} (bal : hˡ ∼ hʳ) ->
          Tree hˡ -> Key ->
          ∃ (\h -> Tree (1 + h) × h ≲ hʳ) ->
          ∃ (\h -> Tree (1 + h) × h ≲ 1 + max bal)
  joinʳ ∼+ t₁ k₂ (._ , node ∼+ t₃ k₄ t₅ , ∼0) = (_ , node ∼0 (node ∼0 t₁ k₂ t₃) k₄ t₅ , ∼+)
  joinʳ ∼+ t₁ k₂ (._ , node ∼0 t₃ k₄ t₅ , ∼0) = (_ , node ∼- (node ∼+ t₁ k₂ t₃) k₄ t₅ , ∼0)
  joinʳ ∼+ t₁ k₂ (._ , node ∼-
                         (node bal t₃ k₄ t₅)
                                  k₆ t₇ , ∼0) = (_ , node (1+ (max∼max bal))
                                                       (node (max∼ bal) t₁ k₂ t₃)
                                                       k₄
                                                       (node (∼max bal) t₅ k₆ t₇)
                                                   , max-lemma bal)
  joinʳ ∼+ t₁ k₂ (._ , t₃ , ∼+) = (_ , node ∼+ t₁ k₂ t₃ , ∼+)
  joinʳ ∼0 t₁ k₂ (_  , t₃ , ∼0) = (_ , node ∼+ t₁ k₂ t₃ , ∼0)
  joinʳ ∼0 t₁ k₂ (_  , t₃ , ∼+) = (_ , node ∼0 t₁ k₂ t₃ , ∼+)
  joinʳ ∼- t₁ k₂ (_  , t₃ , ∼0) = (_ , node ∼0 t₁ k₂ t₃ , ∼+)
  joinʳ ∼- t₁ k₂ (_  , t₃ , ∼+) = (_ , node ∼- t₁ k₂ t₃ , ∼+)

  -- Inserts a key into the tree. If the key already exists, then it
  -- is replaced.

  insert : forall {h} -> Key -> Tree h ->
           ∃ \h′ -> Tree (1 + h′) × h′ ≲ h
  insert k leaf              = (_ , singleton k , ∼0)
  insert k (node bal l k′ r) with compare k k′
  ... | tri< _ _ _ = joinˡ bal (insert k l) k′ r
  ... | tri≈ _ _ _ = (_ , node bal l k r , ∼+)
  ... | tri> _ _ _ = joinʳ bal l k′ (insert k r)

  -- Looks up a key in the tree.

  lookup : forall {h} -> Key -> Tree h -> Maybe Key
  lookup k leaf            = nothing
  lookup k (node h l k′ r) with compare k k′
  ... | tri< _ _ _ = lookup k l
  ... | tri≈ _ _ _ = just k′
  ... | tri> _ _ _ = lookup k r

  -- Converts the tree to an ordered list.

  open DiffList

  toDiffList : forall {h} -> Tree h -> DiffList Key
  toDiffList leaf           = []
  toDiffList (node _ l k r) = toDiffList l ++ [ k ] ++ toDiffList r

------------------------------------------------------------------------
-- Types and functions with hidden indices

data Tree : Set where
  tree : forall {h} -> Indexed.Tree h -> Tree

empty : Tree
empty = tree Indexed.empty

singleton : Key -> Tree
singleton k = tree (Indexed.singleton k)

insert : Key -> Tree -> Tree
insert k (tree t) with Indexed.insert k t
... | (_ , t′ , _) = tree t′

lookup : Key -> Tree -> Maybe Key
lookup k (tree t) = Indexed.lookup k t

-- The input does not need to be ordered.

fromList : List Key -> Tree
fromList = List.foldr insert empty

-- Returns an ordered list.

toList : Tree -> List Key
toList (tree t) = DiffList.toList (Indexed.toDiffList t)
