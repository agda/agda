------------------------------------------------------------------------
-- AVL trees
------------------------------------------------------------------------

-- AVL trees are balanced binary search trees. The search tree
-- invariant is not statically enforced in the current implementation,
-- just the balance invariant.

open import Relation.Binary

module Data.AVL (OrderedKeySet : StrictTotalOrder)
                (Value : StrictTotalOrder.carrier OrderedKeySet → Set)
                where

open import Data.Nat hiding (compare)
open StrictTotalOrder OrderedKeySet renaming (carrier to Key)
open import Data.Product
open import Data.Maybe
open import Data.Bool
open import Data.List as List using (List)
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

  _⊕_ : ℕ₂ → ℕ → ℕ
  0# ⊕ n = n
  1# ⊕ n = 1 + n

  -- i ⊕ n -1 = pred (i ⊕ n).

  _⊕_-1 : ℕ₂ → ℕ → ℕ
  i ⊕ zero  -1 = 0
  i ⊕ suc n -1 = i ⊕ n

  infix 4 _∼_

  -- If m ∼ n, then the difference between m and n is at most 1. _∼_
  -- is used to record the balance factor of the AVL trees, and also
  -- to ensure that the absolute value of the balance factor is never
  -- more than 1.

  data _∼_ : ℕ → ℕ → Set where
    ∼+ : ∀ {n} →     n ∼ 1 + n
    ∼0 : ∀ {n} →     n ∼ n
    ∼- : ∀ {n} → 1 + n ∼ n

  -- The maximum of m and n.

  max : ∀ {m n} → m ∼ n → ℕ
  max (∼+ {n}) = 1 + n
  max (∼0 {n}) =     n
  max (∼- {n}) = 1 + n

  -- Some lemmas.

  1+ : ∀ {m n} → m ∼ n → 1 + m ∼ 1 + n
  1+ ∼+ = ∼+
  1+ ∼0 = ∼0
  1+ ∼- = ∼-

  max∼ : ∀ {i j} (bal : i ∼ j) → max bal ∼ i
  max∼ ∼+ = ∼-
  max∼ ∼0 = ∼0
  max∼ ∼- = ∼0

  ∼max : ∀ {i j} (bal : i ∼ j) → j ∼ max bal
  ∼max ∼+ = ∼0
  ∼max ∼0 = ∼0
  ∼max ∼- = ∼+

  max∼max : ∀ {i j} (bal : i ∼ j) → max (max∼ bal) ∼ max (∼max bal)
  max∼max ∼+ = ∼0
  max∼max ∼0 = ∼0
  max∼max ∼- = ∼0

  max-lemma : ∀ {m n} (bal : m ∼ n) →
              1 + max (1+ (max∼max bal)) ≡ 2 + max bal
  max-lemma ∼+ = refl
  max-lemma ∼0 = refl
  max-lemma ∼- = refl

------------------------------------------------------------------------
-- AVL trees

-- Key/value pairs.

KV : Set
KV = Σ Key Value

module Indexed where

  open Invariants

  -- The trees are indexed on their height. (bal is the balance
  -- factor.)

  data Tree : ℕ → Set where
    leaf : Tree 0
    node : ∀ {hˡ hʳ}
           (l : Tree hˡ) (k : KV) (r : Tree hʳ) (bal : hˡ ∼ hʳ) →
           Tree (1 + max bal)

  -- Various constant-time functions which construct trees out of
  -- smaller pieces, sometimes using rotation.

  joinˡ⁺ : ∀ {hˡ hʳ} →
           (∃ λ i → Tree (i ⊕ hˡ)) → KV → Tree hʳ → (bal : hˡ ∼ hʳ) →
           ∃ λ i → Tree (i ⊕ (1 + max bal))
  joinˡ⁺ (1# , node t₁ k₂
                 (node t₃ k₄ t₅ bal)
                             ∼+) k₆ t₇ ∼-  = (0# , subst Tree (max-lemma bal)
                                                     (node (node t₁ k₂ t₃ (max∼ bal))
                                                           k₄
                                                           (node t₅ k₆ t₇ (∼max bal))
                                                           (1+ (max∼max bal))))
  joinˡ⁺ (1# , node t₁ k₂ t₃ ∼-) k₄ t₅ ∼-  = (0# , node t₁ k₂ (node t₃ k₄ t₅ ∼0) ∼0)
  joinˡ⁺ (1# , node t₁ k₂ t₃ ∼0) k₄ t₅ ∼-  = (1# , node t₁ k₂ (node t₃ k₄ t₅ ∼-) ∼+)
  joinˡ⁺ (1# , t₁)               k₂ t₃ ∼0  = (1# , node t₁ k₂ t₃ ∼-)
  joinˡ⁺ (1# , t₁)               k₂ t₃ ∼+  = (0# , node t₁ k₂ t₃ ∼0)
  joinˡ⁺ (0# , t₁)               k₂ t₃ bal = (0# , node t₁ k₂ t₃ bal)

  joinʳ⁺ : ∀ {hˡ hʳ} →
           Tree hˡ → KV → (∃ λ i → Tree (i ⊕ hʳ)) → (bal : hˡ ∼ hʳ) →
           ∃ λ i → Tree (i ⊕ (1 + max bal))
  joinʳ⁺ t₁ k₂ (1# , node
                       (node t₃ k₄ t₅ bal)
                             k₆ t₇ ∼-) ∼+  = (0# , subst Tree (max-lemma bal)
                                                     (node (node t₁ k₂ t₃ (max∼ bal))
                                                           k₄
                                                           (node t₅ k₆ t₇ (∼max bal))
                                                           (1+ (max∼max bal))))
  joinʳ⁺ t₁ k₂ (1# , node t₃ k₄ t₅ ∼+) ∼+  = (0# , node (node t₁ k₂ t₃ ∼0) k₄ t₅ ∼0)
  joinʳ⁺ t₁ k₂ (1# , node t₃ k₄ t₅ ∼0) ∼+  = (1# , node (node t₁ k₂ t₃ ∼+) k₄ t₅ ∼-)
  joinʳ⁺ t₁ k₂ (1# , t₃)               ∼0  = (1# , node t₁ k₂ t₃ ∼+)
  joinʳ⁺ t₁ k₂ (1# , t₃)               ∼-  = (0# , node t₁ k₂ t₃ ∼0)
  joinʳ⁺ t₁ k₂ (0# , t₃)               bal = (0# , node t₁ k₂ t₃ bal)

  joinˡ⁻ : ∀ hˡ {hʳ} →
           (∃ λ i → Tree (i ⊕ hˡ -1)) → KV → Tree hʳ → (bal : hˡ ∼ hʳ) →
           ∃ λ i → Tree (i ⊕ max bal)
  joinˡ⁻ zero    (0# , t₁) k₂ t₃ bal = (1# , node t₁ k₂ t₃ bal)
  joinˡ⁻ zero    (1# , t₁) k₂ t₃ bal = (1# , node t₁ k₂ t₃ bal)
  joinˡ⁻ (suc _) (0# , t₁) k₂ t₃ ∼+  = joinʳ⁺ t₁ k₂ (1# , t₃) ∼+
  joinˡ⁻ (suc _) (0# , t₁) k₂ t₃ ∼0  = (1# , node t₁ k₂ t₃ ∼+)
  joinˡ⁻ (suc _) (0# , t₁) k₂ t₃ ∼-  = (0# , node t₁ k₂ t₃ ∼0)
  joinˡ⁻ (suc _) (1# , t₁) k₂ t₃ bal = (1# , node t₁ k₂ t₃ bal)

  joinʳ⁻ : ∀ {hˡ} hʳ →
           Tree hˡ → KV → (∃ λ i → Tree (i ⊕ hʳ -1)) → (bal : hˡ ∼ hʳ) →
           ∃ λ i → Tree (i ⊕ max bal)
  joinʳ⁻ zero    t₁ k₂ (0# , t₃) bal = (1# , node t₁ k₂ t₃ bal)
  joinʳ⁻ zero    t₁ k₂ (1# , t₃) bal = (1# , node t₁ k₂ t₃ bal)
  joinʳ⁻ (suc _) t₁ k₂ (0# , t₃) ∼-  = joinˡ⁺ (1# , t₁) k₂ t₃ ∼-
  joinʳ⁻ (suc _) t₁ k₂ (0# , t₃) ∼0  = (1# , node t₁ k₂ t₃ ∼-)
  joinʳ⁻ (suc _) t₁ k₂ (0# , t₃) ∼+  = (0# , node t₁ k₂ t₃ ∼0)
  joinʳ⁻ (suc _) t₁ k₂ (1# , t₃) bal = (1# , node t₁ k₂ t₃ bal)

  -- Extracts the smallest element from the tree, plus the rest.
  -- Logarithmic in the size of the tree.

  headTail : ∀ {h} → Tree (1 + h) →
             KV × ∃ λ i → Tree (i ⊕ h)
  headTail (node leaf k₁ t₂ ∼+) = (k₁ , 0# , t₂)
  headTail (node leaf k₁ t₂ ∼0) = (k₁ , 0# , t₂)
  headTail (node {hˡ = suc _} t₁₂ k₃ t₄ bal) with headTail t₁₂
  ... | (k₁ , t₂) = (k₁ , joinˡ⁻ _ t₂ k₃ t₄ bal)

  -- Extracts the largest element from the tree, plus the rest.
  -- Logarithmic in the size of the tree.

  initLast : ∀ {h} → Tree (1 + h) →
             ∃ (λ i → Tree (i ⊕ h)) × KV
  initLast (node t₁ k₂ leaf ∼-) = ((0# , t₁) , k₂)
  initLast (node t₁ k₂ leaf ∼0) = ((0# , t₁) , k₂)
  initLast (node {hʳ = suc _} t₁ k₂ t₃₄ bal) with initLast t₃₄
  ... | (t₃ , k₄) = (joinʳ⁻ _ t₁ k₂ t₃ bal , k₄)

  -- Another joining function. Logarithmic in the size of the tree.

  join : ∀ {hˡ hʳ} →
         Tree hˡ → Tree hʳ → (bal : hˡ ∼ hʳ) →
         ∃ λ i → Tree (i ⊕ max bal)
  join t₁ leaf ∼0 = (0# , t₁)
  join t₁ leaf ∼- = (0# , t₁)
  join {hʳ = suc _} t₁ t₂₃ bal with headTail t₂₃
  ... | (k₂ , t₃) = joinʳ⁻ _ t₁ k₂ t₃ bal

  -- An empty tree.

  empty : Tree 0
  empty = leaf

  -- A singleton tree.

  singleton : (k : Key) → Value k → Tree 1
  singleton k v = node leaf (k , v) leaf ∼0

  -- Inserts a key into the tree. If the key already exists, then it
  -- is replaced. Logarithmic in the size of the tree (assuming
  -- constant-time comparisons).

  insert : ∀ {h} → (k : Key) → Value k → Tree h →
           ∃ λ i → Tree (i ⊕ h)
  insert k v leaf             = (1# , singleton k v)
  insert k v (node l p r bal) with compare k (proj₁ p)
  ... | tri< _ _ _ = joinˡ⁺ (insert k v l) p r bal
  ... | tri≈ _ _ _ = (0# , node l (k , v) r bal)
  ... | tri> _ _ _ = joinʳ⁺ l p (insert k v r) bal

  -- Deletes the key/value pair containing the given key, if any.
  -- Logarithmic in the size of the tree (assuming constant-time
  -- comparisons).

  delete : ∀ {h} → Key → Tree h →
           ∃ λ i → Tree (i ⊕ h -1)
  delete k leaf             = (0# , leaf)
  delete k (node l p r bal) with compare k (proj₁ p)
  ... | tri< _ _ _ = joinˡ⁻ _ (delete k l) p r bal
  ... | tri≈ _ _ _ = join l r bal
  ... | tri> _ _ _ = joinʳ⁻ _ l p (delete k r) bal

  -- Looks up a key in the tree. Logarithmic in the size of the tree
  -- (assuming constant-time comparisons).

  lookup : ∀ {h} → (k : Key) → Tree h →
           Maybe (∃ λ k′ → Value k′ × k ≈ k′)
  lookup k leaf                  = nothing
  lookup k (node l (k′ , v) r _) with compare k k′
  ... | tri< _ _  _ = lookup k l
  ... | tri≈ _ eq _ = just (k′ , v , eq)
  ... | tri> _ _  _ = lookup k r

  -- Converts the tree to an ordered list. Linear in the size of the
  -- tree.

  open DiffList

  toDiffList : ∀ {h} → Tree h → DiffList KV
  toDiffList leaf           = []
  toDiffList (node l k r _) = toDiffList l ++ [ k ] ++ toDiffList r

------------------------------------------------------------------------
-- Types and functions with hidden indices

data Tree : Set where
  tree : ∀ {h} → Indexed.Tree h → Tree

empty : Tree
empty = tree Indexed.empty

singleton : (k : Key) → Value k → Tree
singleton k v = tree (Indexed.singleton k v)

insert : (k : Key) → Value k → Tree → Tree
insert k v (tree t) with Indexed.insert k v t
... | (_ , t′) = tree t′

delete : Key → Tree → Tree
delete k (tree t) with Indexed.delete k t
... | (_ , t′) = tree t′

lookup : (k : Key) → Tree → Maybe (∃ λ k′ → Value k′ × k ≈ k′)
lookup k (tree t) = Indexed.lookup k t

_∈?_ : Key → Tree → Bool
k ∈? t = maybeToBool (lookup k t)

headTail : Tree → Maybe (KV × Tree)
headTail (tree Indexed.leaf)  = nothing
headTail (tree {h = suc _} t) with Indexed.headTail t
... | (k , _ , t′) = just (k , tree t′)

initLast : Tree → Maybe (Tree × KV)
initLast (tree Indexed.leaf)  = nothing
initLast (tree {h = suc _} t) with Indexed.initLast t
... | ((_ , t′) , k) = just (tree t′ , k)

-- The input does not need to be ordered.

fromList : List KV → Tree
fromList = List.foldr (uncurry insert) empty

-- Returns an ordered list.

toList : Tree → List KV
toList (tree t) = DiffList.toList (Indexed.toDiffList t)
