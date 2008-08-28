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
open import Data.Bool
import Data.List as List
open List using (List)
import Data.DifferenceList as DiffList
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Types and functions which are used to keep track of invariants

module Invariants where

  -- Bits. (I would use Fin 2 instead if Agda had "defined patterns",
  -- so that I could pattern match on 1# instead of suc zero; the text
  -- "suc zero" takes up a lot more space.)

  data ℕ₂ : Set where
    0# : ℕ₂
    1# : ℕ₂

  -- Addition.

  infixl 6 _⊕_

  _⊕_ : ℕ₂ -> ℕ -> ℕ
  0# ⊕ n = n
  1# ⊕ n = 1 + n

  -- i ⊕ n -1 = pred (i ⊕ n).

  _⊕_-1 : ℕ₂ -> ℕ -> ℕ
  i ⊕ zero  -1 = 0
  i ⊕ suc n -1 = i ⊕ n

  infix 4 _∼_

  -- If m ∼ n, then the difference between m and n is at most 1. _∼_
  -- is used to record the balance factor of the AVL trees, and also
  -- to ensure that the absolute value of the balance factor is never
  -- more than 1.

  data _∼_ : ℕ -> ℕ -> Set where
    ∼+ : forall {n} ->     n ∼ 1 + n
    ∼0 : forall {n} ->     n ∼ n
    ∼- : forall {n} -> 1 + n ∼ n

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
              1 + max (1+ (max∼max bal)) ≡ 2 + max bal
  max-lemma ∼+ = ≡-refl
  max-lemma ∼0 = ≡-refl
  max-lemma ∼- = ≡-refl

------------------------------------------------------------------------
-- AVL trees

module Indexed where

  open Invariants

  -- The trees are indexed on their height. (bal is the balance
  -- factor.)

  data Tree : ℕ -> Set where
    leaf : Tree 0
    node : forall {hˡ hʳ}
           (l : Tree hˡ) (k : Key) (r : Tree hʳ) (bal : hˡ ∼ hʳ) ->
           Tree (1 + max bal)

  -- Various constant-time functions which construct trees out of
  -- smaller pieces, sometimes using rotation.

  joinˡ⁺ : forall {hˡ hʳ} ->
           (∃ \i -> Tree (i ⊕ hˡ)) -> Key -> Tree hʳ ->
           (bal : hˡ ∼ hʳ) ->
           ∃ \i -> Tree (i ⊕ (1 + max bal))
  joinˡ⁺ (1# , node t₁ k₂
                 (node t₃ k₄ t₅ bal)
                             ∼+) k₆ t₇ ∼-  = (0# , ≡-subst Tree (max-lemma bal)
                                                     (node (node t₁ k₂ t₃ (max∼ bal))
                                                           k₄
                                                           (node t₅ k₆ t₇ (∼max bal))
                                                           (1+ (max∼max bal))))
  joinˡ⁺ (1# , node t₁ k₂ t₃ ∼-) k₄ t₅ ∼-  = (0# , node t₁ k₂ (node t₃ k₄ t₅ ∼0) ∼0)
  joinˡ⁺ (1# , node t₁ k₂ t₃ ∼0) k₄ t₅ ∼-  = (1# , node t₁ k₂ (node t₃ k₄ t₅ ∼-) ∼+)
  joinˡ⁺ (1# , t₁)               k₂ t₃ ∼0  = (1# , node t₁ k₂ t₃ ∼-)
  joinˡ⁺ (1# , t₁)               k₂ t₃ ∼+  = (0# , node t₁ k₂ t₃ ∼0)
  joinˡ⁺ (0# , t₁)               k₂ t₃ bal = (0# , node t₁ k₂ t₃ bal)

  joinʳ⁺ : forall {hˡ hʳ} ->
           Tree hˡ -> Key -> (∃ \i -> Tree (i ⊕ hʳ)) ->
           (bal : hˡ ∼ hʳ) ->
           ∃ \i -> Tree (i ⊕ (1 + max bal))
  joinʳ⁺ t₁ k₂ (1# , node
                       (node t₃ k₄ t₅ bal)
                             k₆ t₇ ∼-) ∼+  = (0# , ≡-subst Tree (max-lemma bal)
                                                     (node (node t₁ k₂ t₃ (max∼ bal))
                                                           k₄
                                                           (node t₅ k₆ t₇ (∼max bal))
                                                           (1+ (max∼max bal))))
  joinʳ⁺ t₁ k₂ (1# , node t₃ k₄ t₅ ∼+) ∼+  = (0# , node (node t₁ k₂ t₃ ∼0) k₄ t₅ ∼0)
  joinʳ⁺ t₁ k₂ (1# , node t₃ k₄ t₅ ∼0) ∼+  = (1# , node (node t₁ k₂ t₃ ∼+) k₄ t₅ ∼-)
  joinʳ⁺ t₁ k₂ (1# , t₃)               ∼0  = (1# , node t₁ k₂ t₃ ∼+)
  joinʳ⁺ t₁ k₂ (1# , t₃)               ∼-  = (0# , node t₁ k₂ t₃ ∼0)
  joinʳ⁺ t₁ k₂ (0# , t₃)               bal = (0# , node t₁ k₂ t₃ bal)

  joinˡ⁻ : forall hˡ {hʳ} ->
           (∃ \i -> Tree (i ⊕ hˡ -1)) -> Key -> Tree hʳ ->
           (bal : hˡ ∼ hʳ) ->
           ∃ \i -> Tree (i ⊕ max bal)
  joinˡ⁻ zero    (0# , t₁) k₂ t₃ bal = (1# , node t₁ k₂ t₃ bal)
  joinˡ⁻ zero    (1# , t₁) k₂ t₃ bal = (1# , node t₁ k₂ t₃ bal)
  joinˡ⁻ (suc _) (0# , t₁) k₂ t₃ ∼+  = joinʳ⁺ t₁ k₂ (1# , t₃) ∼+
  joinˡ⁻ (suc _) (0# , t₁) k₂ t₃ ∼0  = (1# , node t₁ k₂ t₃ ∼+)
  joinˡ⁻ (suc _) (0# , t₁) k₂ t₃ ∼-  = (0# , node t₁ k₂ t₃ ∼0)
  joinˡ⁻ (suc _) (1# , t₁) k₂ t₃ bal = (1# , node t₁ k₂ t₃ bal)

  joinʳ⁻ : forall {hˡ} hʳ ->
           Tree hˡ -> Key -> (∃ \i -> Tree (i ⊕ hʳ -1)) ->
           (bal : hˡ ∼ hʳ) ->
           ∃ \i -> Tree (i ⊕ max bal)
  joinʳ⁻ zero    t₁ k₂ (0# , t₃) bal = (1# , node t₁ k₂ t₃ bal)
  joinʳ⁻ zero    t₁ k₂ (1# , t₃) bal = (1# , node t₁ k₂ t₃ bal)
  joinʳ⁻ (suc _) t₁ k₂ (0# , t₃) ∼-  = joinˡ⁺ (1# , t₁) k₂ t₃ ∼-
  joinʳ⁻ (suc _) t₁ k₂ (0# , t₃) ∼0  = (1# , node t₁ k₂ t₃ ∼-)
  joinʳ⁻ (suc _) t₁ k₂ (0# , t₃) ∼+  = (0# , node t₁ k₂ t₃ ∼0)
  joinʳ⁻ (suc _) t₁ k₂ (1# , t₃) bal = (1# , node t₁ k₂ t₃ bal)

  -- Extracts the smallest element from the tree, plus the rest.
  -- Logarithmic in the size of the tree.

  headTail : forall {h} -> Tree (1 + h) ->
             Key × ∃ \i -> Tree (i ⊕ h)
  headTail (node leaf k₁ t₂ ∼+) = (k₁ , 0# , t₂)
  headTail (node leaf k₁ t₂ ∼0) = (k₁ , 0# , t₂)
  headTail (node {hˡ = suc _} t₁₂ k₃ t₄ bal) with headTail t₁₂
  ... | (k₁ , t₂) = (k₁ , joinˡ⁻ _ t₂ k₃ t₄ bal)

  -- Extracts the largest element from the tree, plus the rest.
  -- Logarithmic in the size of the tree.

  initLast : forall {h} -> Tree (1 + h) ->
             ∃ (\i -> Tree (i ⊕ h)) × Key
  initLast (node t₁ k₂ leaf ∼-) = ((0# , t₁) , k₂)
  initLast (node t₁ k₂ leaf ∼0) = ((0# , t₁) , k₂)
  initLast (node {hʳ = suc _} t₁ k₂ t₃₄ bal) with initLast t₃₄
  ... | (t₃ , k₄) = (joinʳ⁻ _ t₁ k₂ t₃ bal , k₄)

  -- Another joining function. Logarithmic in the size of the tree.

  join : forall {hˡ hʳ} ->
         Tree hˡ -> Tree hʳ -> (bal : hˡ ∼ hʳ) ->
         ∃ \i -> Tree (i ⊕ max bal)
  join t₁ leaf ∼0 = (0# , t₁)
  join t₁ leaf ∼- = (0# , t₁)
  join {hʳ = suc _} t₁ t₂₃ bal with headTail t₂₃
  ... | (k₂ , t₃) = joinʳ⁻ _ t₁ k₂ t₃ bal

  -- An empty tree.

  empty : Tree 0
  empty = leaf

  -- A singleton tree.

  singleton : Key -> Tree 1
  singleton k = node leaf k leaf ∼0

  -- Inserts a key into the tree. If the key already exists, then it
  -- is replaced. Logarithmic in the size of the tree.

  insert : forall {h} -> Key -> Tree h ->
           ∃ \i -> Tree (i ⊕ h)
  insert k leaf              = (1# , singleton k)
  insert k (node l k′ r bal) with compare k k′
  ... | tri< _ _ _ = joinˡ⁺ (insert k l) k′ r bal
  ... | tri≈ _ _ _ = (0# , node l k r bal)
  ... | tri> _ _ _ = joinʳ⁺ l k′ (insert k r) bal

  -- Deletes the key/value pair containing the given key, if any.
  -- Logarithmic in the size of the tree.

  delete : forall {h} -> Key -> Tree h ->
           ∃ \i -> Tree (i ⊕ h -1)
  delete k leaf              = (0# , leaf)
  delete k (node l k′ r bal) with compare k k′
  ... | tri< _ _ _ = joinˡ⁻ _ (delete k l) k′ r bal
  ... | tri≈ _ _ _ = join l r bal
  ... | tri> _ _ _ = joinʳ⁻ _ l k′ (delete k r) bal

  -- Looks up a key in the tree. Logarithmic in the size of the tree.

  lookup : forall {h} -> Key -> Tree h -> Maybe Key
  lookup k leaf            = nothing
  lookup k (node l k′ r _) with compare k k′
  ... | tri< _ _ _ = lookup k l
  ... | tri≈ _ _ _ = just k′
  ... | tri> _ _ _ = lookup k r

  -- Converts the tree to an ordered list. Linear in the size of the
  -- tree.

  open DiffList

  toDiffList : forall {h} -> Tree h -> DiffList Key
  toDiffList leaf           = []
  toDiffList (node l k r _) = toDiffList l ++ [ k ] ++ toDiffList r

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
... | (_ , t′) = tree t′

delete : Key -> Tree -> Tree
delete k (tree t) with Indexed.delete k t
... | (_ , t′) = tree t′

lookup : Key -> Tree -> Maybe Key
lookup k (tree t) = Indexed.lookup k t

_∈?_ : Key -> Tree -> Bool
k ∈? t = maybeToBool (lookup k t)

headTail : Tree -> Maybe (Key × Tree)
headTail (tree leaf)          = nothing
headTail (tree {h = suc _} t) with Indexed.headTail t
... | (k , _ , t′) = just (k , tree t′)

initLast : Tree -> Maybe (Tree × Key)
initLast (tree leaf)          = nothing
initLast (tree {h = suc _} t) with Indexed.initLast t
... | ((_ , t′) , k) = just (tree t′ , k)

-- The input does not need to be ordered.

fromList : List Key -> Tree
fromList = List.foldr insert empty

-- Returns an ordered list.

toList : Tree -> List Key
toList (tree t) = DiffList.toList (Indexed.toDiffList t)
