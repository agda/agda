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
  {k v ℓ}
  {Key : Set k} (Value : Key → Set v)
  {_<_ : Rel Key ℓ}
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

------------------------------------------------------------------------
-- Extended keys

module Extended-key where

  -- The key type extended with a new minimum and maximum.

  data Key⁺ : Set k where
    ⊥⁺ ⊤⁺ : Key⁺
    [_]   : (k : Key) → Key⁺

  [_]-injective : ∀ {k l} → [ k ] ≡ [ l ] → k ≡ l
  [_]-injective refl = refl

  -- An extended strict ordering relation.

  infix 4 _<⁺_

  _<⁺_ : Key⁺ → Key⁺ → Set ℓ
  ⊥⁺    <⁺ [ _ ] = Lift ⊤
  ⊥⁺    <⁺ ⊤⁺    = Lift ⊤
  [ x ] <⁺ [ y ] = x < y
  [ _ ] <⁺ ⊤⁺    = Lift ⊤
  _     <⁺ _     = Lift ⊥

  -- A pair of ordering constraints.

  infix 4 _<_<_

  _<_<_ : Key⁺ → Key → Key⁺ → Set ℓ
  l < x < u = l <⁺ [ x ] × [ x ] <⁺ u

  -- _<⁺_ is transitive.

  trans⁺ : ∀ l {m u} → l <⁺ m → m <⁺ u → l <⁺ u

  trans⁺ [ l ] {m = [ m ]} {u = [ u ]} l<m m<u = trans l<m m<u

  trans⁺ ⊥⁺    {u = [ _ ]} _ _ = _
  trans⁺ ⊥⁺    {u = ⊤⁺}    _ _ = _
  trans⁺ [ _ ] {u = ⊤⁺}    _ _ = _

  trans⁺ _     {m = ⊥⁺}    {u = ⊥⁺}    _ (lift ())
  trans⁺ _     {m = [ _ ]} {u = ⊥⁺}    _ (lift ())
  trans⁺ _     {m = ⊤⁺}    {u = ⊥⁺}    _ (lift ())
  trans⁺ [ _ ] {m = ⊥⁺}    {u = [ _ ]} (lift ()) _
  trans⁺ [ _ ] {m = ⊤⁺}    {u = [ _ ]} _ (lift ())
  trans⁺ ⊤⁺    {m = ⊥⁺}                (lift ()) _
  trans⁺ ⊤⁺    {m = [ _ ]}             (lift ()) _
  trans⁺ ⊤⁺    {m = ⊤⁺}                (lift ()) _

------------------------------------------------------------------------
-- Types and functions which are used to keep track of height
-- invariants

module Height-invariants where

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

  -- pred[ i ⊕ n ] = pred (i ⊕ n).

  pred[_⊕_] : ℕ₂ → ℕ → ℕ
  pred[ i ⊕ zero  ] = 0
  pred[ i ⊕ suc n ] = i ⊕ n

  infix 4 _∼_⊔_

  -- If i ∼ j ⊔ m, then the difference between i and j is at most 1,
  -- and the maximum of i and j is m. _∼_⊔_ is used to record the
  -- balance factor of the AVL trees, and also to ensure that the
  -- absolute value of the balance factor is never more than 1.

  data _∼_⊔_ : ℕ → ℕ → ℕ → Set where
    ∼+ : ∀ {n} →     n ∼ 1 + n ⊔ 1 + n
    ∼0 : ∀ {n} →     n ∼ n     ⊔ n
    ∼- : ∀ {n} → 1 + n ∼ n     ⊔ 1 + n

  -- Some lemmas.

  max∼ : ∀ {i j m} → i ∼ j ⊔ m → m ∼ i ⊔ m
  max∼ ∼+ = ∼-
  max∼ ∼0 = ∼0
  max∼ ∼- = ∼0

  ∼max : ∀ {i j m} → i ∼ j ⊔ m → j ∼ m ⊔ m
  ∼max ∼+ = ∼0
  ∼max ∼0 = ∼0
  ∼max ∼- = ∼+

------------------------------------------------------------------------
-- AVL trees

-- Key/value pairs.

KV : Set (k ⊔ v)
KV = Σ Key Value

module Indexed where

  open Extended-key
  open Height-invariants

  -- The trees have three parameters/indices: a lower bound on the
  -- keys, an upper bound, and a height.
  --
  -- (The bal argument is the balance factor.)

  data Tree (l u : Key⁺) : ℕ → Set (k ⊔ v ⊔ ℓ) where
    leaf : (l<u : l <⁺ u) → Tree l u 0
    node : ∀ {hˡ hʳ h}
           (k : KV)
           (lk : Tree l [ proj₁ k ] hˡ)
           (ku : Tree [ proj₁ k ] u hʳ)
           (bal : hˡ ∼ hʳ ⊔ h) →
           Tree l u (suc h)

  leaf-injective : ∀ {l u} {p q : l <⁺ u} → (Tree l u 0 ∋ leaf p) ≡ leaf q → p ≡ q
  leaf-injective refl = refl

  node-injective-key : ∀ {hˡ hʳ h l u k₁ k₂}
    {lk₁ : Tree l [ proj₁ k₁ ] hˡ} {lk₂ : Tree l [ proj₁ k₂ ] hˡ}
    {ku₁ : Tree [ proj₁ k₁ ] u hʳ} {ku₂ : Tree [ proj₁ k₂ ] u hʳ}
    {bal₁ bal₂ : hˡ ∼ hʳ ⊔ h} → node k₁ lk₁ ku₁ bal₁ ≡ node k₂ lk₂ ku₂ bal₂ → k₁ ≡ k₂
  node-injective-key refl = refl

  node-injectiveˡ : ∀ {hˡ hʳ h l u k}
    {lk₁ : Tree l [ proj₁ k ] hˡ} {lk₂ : Tree l [ proj₁ k ] hˡ}
    {ku₁ : Tree [ proj₁ k ] u hʳ} {ku₂ : Tree [ proj₁ k ] u hʳ}
    {bal₁ bal₂ : hˡ ∼ hʳ ⊔ h} → node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → lk₁ ≡ lk₂
  node-injectiveˡ refl = refl

  node-injectiveʳ : ∀ {hˡ hʳ h l u k}
    {lk₁ : Tree l [ proj₁ k ] hˡ} {lk₂ : Tree l [ proj₁ k ] hˡ}
    {ku₁ : Tree [ proj₁ k ] u hʳ} {ku₂ : Tree [ proj₁ k ] u hʳ}
    {bal₁ bal₂ : hˡ ∼ hʳ ⊔ h} → node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → ku₁ ≡ ku₂
  node-injectiveʳ refl = refl

  node-injective-bal : ∀ {hˡ hʳ h l u k}
    {lk₁ : Tree l [ proj₁ k ] hˡ} {lk₂ : Tree l [ proj₁ k ] hˡ}
    {ku₁ : Tree [ proj₁ k ] u hʳ} {ku₂ : Tree [ proj₁ k ] u hʳ}
    {bal₁ bal₂ : hˡ ∼ hʳ ⊔ h} → node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → bal₁ ≡ bal₂
  node-injective-bal refl = refl

  -- Cast operations. Logarithmic in the size of the tree, if we don't
  -- count the time needed to construct the new proofs in the leaf
  -- cases. (The same kind of caveat applies to other operations
  -- below.)
  --
  -- Perhaps it would be worthwhile changing the data structure so
  -- that the casts could be implemented in constant time (excluding
  -- proof manipulation). However, note that this would not change the
  -- worst-case time complexity of the operations below (up to Θ).

  castˡ : ∀ {l m u h} → l <⁺ m → Tree m u h → Tree l u h
  castˡ {l} l<m (leaf m<u)         = leaf (trans⁺ l l<m m<u)
  castˡ     l<m (node k mk ku bal) = node k (castˡ l<m mk) ku bal

  castʳ : ∀ {l m u h} → Tree l m h → m <⁺ u → Tree l u h
  castʳ {l} (leaf l<m)         m<u = leaf (trans⁺ l l<m m<u)
  castʳ     (node k lk km bal) m<u = node k lk (castʳ km m<u) bal

  -- Various constant-time functions which construct trees out of
  -- smaller pieces, sometimes using rotation.

  joinˡ⁺ : ∀ {l u hˡ hʳ h} →
           (k : KV) →
           (∃ λ i → Tree l [ proj₁ k ] (i ⊕ hˡ)) →
           Tree [ proj₁ k ] u hʳ →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Tree l u (i ⊕ (1 + h))
  joinˡ⁺ k₆ (1# , node k₂ t₁
                    (node k₄ t₃ t₅ bal)
                                ∼+) t₇ ∼-  = (0# , node k₄
                                                        (node k₂ t₁ t₃ (max∼ bal))
                                                        (node k₆ t₅ t₇ (∼max bal))
                                                        ∼0)
  joinˡ⁺ k₄ (1# , node k₂ t₁ t₃ ∼-) t₅ ∼-  = (0# , node k₂ t₁ (node k₄ t₃ t₅ ∼0) ∼0)
  joinˡ⁺ k₄ (1# , node k₂ t₁ t₃ ∼0) t₅ ∼-  = (1# , node k₂ t₁ (node k₄ t₃ t₅ ∼-) ∼+)
  joinˡ⁺ k₂ (1# , t₁)               t₃ ∼0  = (1# , node k₂ t₁ t₃ ∼-)
  joinˡ⁺ k₂ (1# , t₁)               t₃ ∼+  = (0# , node k₂ t₁ t₃ ∼0)
  joinˡ⁺ k₂ (0# , t₁)               t₃ bal = (0# , node k₂ t₁ t₃ bal)

  joinʳ⁺ : ∀ {l u hˡ hʳ h} →
           (k : KV) →
           Tree l [ proj₁ k ] hˡ →
           (∃ λ i → Tree [ proj₁ k ] u (i ⊕ hʳ)) →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Tree l u (i ⊕ (1 + h))
  joinʳ⁺ k₂ t₁ (1# , node k₆
                       (node k₄ t₃ t₅ bal)
                                t₇ ∼-) ∼+  = (0# , node k₄
                                                        (node k₂ t₁ t₃ (max∼ bal))
                                                        (node k₆ t₅ t₇ (∼max bal))
                                                        ∼0)
  joinʳ⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼+) ∼+  = (0# , node k₄ (node k₂ t₁ t₃ ∼0) t₅ ∼0)
  joinʳ⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼0) ∼+  = (1# , node k₄ (node k₂ t₁ t₃ ∼+) t₅ ∼-)
  joinʳ⁺ k₂ t₁ (1# , t₃)               ∼0  = (1# , node k₂ t₁ t₃ ∼+)
  joinʳ⁺ k₂ t₁ (1# , t₃)               ∼-  = (0# , node k₂ t₁ t₃ ∼0)
  joinʳ⁺ k₂ t₁ (0# , t₃)               bal = (0# , node k₂ t₁ t₃ bal)

  joinˡ⁻ : ∀ {l u} hˡ {hʳ h} →
           (k : KV) →
           (∃ λ i → Tree l [ proj₁ k ] pred[ i ⊕ hˡ ]) →
           Tree [ proj₁ k ] u hʳ →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Tree l u (i ⊕ h)
  joinˡ⁻ zero    k₂ (0# , t₁) t₃ bal = (1# , node k₂ t₁ t₃ bal)
  joinˡ⁻ zero    k₂ (1# , t₁) t₃ bal = (1# , node k₂ t₁ t₃ bal)
  joinˡ⁻ (suc _) k₂ (0# , t₁) t₃ ∼+  = joinʳ⁺ k₂ t₁ (1# , t₃) ∼+
  joinˡ⁻ (suc _) k₂ (0# , t₁) t₃ ∼0  = (1# , node k₂ t₁ t₃ ∼+)
  joinˡ⁻ (suc _) k₂ (0# , t₁) t₃ ∼-  = (0# , node k₂ t₁ t₃ ∼0)
  joinˡ⁻ (suc _) k₂ (1# , t₁) t₃ bal = (1# , node k₂ t₁ t₃ bal)

  joinʳ⁻ : ∀ {l u hˡ} hʳ {h} →
           (k : KV) →
           Tree l [ proj₁ k ] hˡ →
           (∃ λ i → Tree [ proj₁ k ] u pred[ i ⊕ hʳ ]) →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Tree l u (i ⊕ h)
  joinʳ⁻ zero    k₂ t₁ (0# , t₃) bal = (1# , node k₂ t₁ t₃ bal)
  joinʳ⁻ zero    k₂ t₁ (1# , t₃) bal = (1# , node k₂ t₁ t₃ bal)
  joinʳ⁻ (suc _) k₂ t₁ (0# , t₃) ∼-  = joinˡ⁺ k₂ (1# , t₁) t₃ ∼-
  joinʳ⁻ (suc _) k₂ t₁ (0# , t₃) ∼0  = (1# , node k₂ t₁ t₃ ∼-)
  joinʳ⁻ (suc _) k₂ t₁ (0# , t₃) ∼+  = (0# , node k₂ t₁ t₃ ∼0)
  joinʳ⁻ (suc _) k₂ t₁ (1# , t₃) bal = (1# , node k₂ t₁ t₃ bal)

  -- Extracts the smallest element from the tree, plus the rest.
  -- Logarithmic in the size of the tree.

  headTail : ∀ {l u h} → Tree l u (1 + h) →
             ∃ λ (k : KV) → l <⁺ [ proj₁ k ] ×
                            ∃ λ i → Tree [ proj₁ k ] u (i ⊕ h)
  headTail (node k₁ (leaf l<k₁) t₂ ∼+) = (k₁ , l<k₁ , 0# , t₂)
  headTail (node k₁ (leaf l<k₁) t₂ ∼0) = (k₁ , l<k₁ , 0# , t₂)
  headTail (node {hˡ = suc _} k₃ t₁₂ t₄ bal) with headTail t₁₂
  ... | (k₁ , l<k₁ , t₂) = (k₁ , l<k₁ , joinˡ⁻ _ k₃ t₂ t₄ bal)

  -- Extracts the largest element from the tree, plus the rest.
  -- Logarithmic in the size of the tree.

  initLast : ∀ {l u h} → Tree l u (1 + h) →
             ∃ λ (k : KV) → [ proj₁ k ] <⁺ u ×
                            ∃ λ i → Tree l [ proj₁ k ] (i ⊕ h)
  initLast (node k₂ t₁ (leaf k₂<u) ∼-) = (k₂ , k₂<u , (0# , t₁))
  initLast (node k₂ t₁ (leaf k₂<u) ∼0) = (k₂ , k₂<u , (0# , t₁))
  initLast (node {hʳ = suc _} k₂ t₁ t₃₄ bal) with initLast t₃₄
  ... | (k₄ , k₄<u , t₃) = (k₄ , k₄<u , joinʳ⁻ _ k₂ t₁ t₃ bal)

  -- Another joining function. Logarithmic in the size of either of
  -- the input trees (which need to have almost equal heights).

  join : ∀ {l m u hˡ hʳ h} →
         Tree l m hˡ → Tree m u hʳ → (bal : hˡ ∼ hʳ ⊔ h) →
         ∃ λ i → Tree l u (i ⊕ h)
  join t₁ (leaf m<u) ∼0 = (0# , castʳ t₁ m<u)
  join t₁ (leaf m<u) ∼- = (0# , castʳ t₁ m<u)
  join {hʳ = suc _} t₁ t₂₃ bal with headTail t₂₃
  ... | (k₂ , m<k₂ , t₃) = joinʳ⁻ _ k₂ (castʳ t₁ m<k₂) t₃ bal

  -- An empty tree.

  empty : ∀ {l u} → l <⁺ u → Tree l u 0
  empty = leaf

  -- A singleton tree.

  singleton : ∀ {l u} (k : Key) → Value k → l < k < u → Tree l u 1
  singleton k v (l<k , k<u) = node (k , v) (leaf l<k) (leaf k<u) ∼0

  -- Inserts a key into the tree, using a function to combine any
  -- existing value with the new value. Logarithmic in the size of the
  -- tree (assuming constant-time comparisons and a constant-time
  -- combining function).

  insertWith : ∀ {l u h} → (k : Key) → Value k →
               (Value k → Value k → Value k) →  -- New → old → result.
               Tree l u h → l < k < u →
               ∃ λ i → Tree l u (i ⊕ h)
  insertWith k v f (leaf l<u) l<k<u = (1# , singleton k v l<k<u)
  insertWith k v f (node (k′ , v′) lp pu bal) (l<k , k<u) with compare k k′
  ... | tri< k<k′ _ _ = joinˡ⁺ (k′ , v′) (insertWith k v f lp (l<k , k<k′)) pu bal
  ... | tri> _ _ k′<k = joinʳ⁺ (k′ , v′) lp (insertWith k v f pu (k′<k , k<u)) bal
  ... | tri≈ _ k≡k′ _ rewrite P.sym k≡k′ = (0# , node (k , f v v′) lp pu bal)

  -- Inserts a key into the tree. If the key already exists, then it
  -- is replaced. Logarithmic in the size of the tree (assuming
  -- constant-time comparisons).

  insert : ∀ {l u h} → (k : Key) → Value k → Tree l u h → l < k < u →
           ∃ λ i → Tree l u (i ⊕ h)
  insert k v = insertWith k v const

  -- Deletes the key/value pair containing the given key, if any.
  -- Logarithmic in the size of the tree (assuming constant-time
  -- comparisons).

  delete : ∀ {l u h} → Key → Tree l u h →
           ∃ λ i → Tree l u pred[ i ⊕ h ]
  delete k (leaf l<u)         = (0# , leaf l<u)
  delete k (node p lp pu bal) with compare k (proj₁ p)
  ... | tri< _ _ _ = joinˡ⁻ _ p (delete k lp) pu bal
  ... | tri> _ _ _ = joinʳ⁻ _ p lp (delete k pu) bal
  ... | tri≈ _ _ _ = join lp pu bal

  -- Looks up a key. Logarithmic in the size of the tree (assuming
  -- constant-time comparisons).

  lookup : ∀ {l u h} → (k : Key) → Tree l u h → Maybe (Value k)
  lookup k (leaf _)                  = nothing
  lookup k (node (k′ , v) lk′ k′u _) with compare k k′
  ... | tri< _ _  _ = lookup k lk′
  ... | tri> _ _  _ = lookup k k′u
  ... | tri≈ _ eq _ rewrite eq = just v

  -- Maps a function over all values in the tree.

  map : (∀ {k} → Value k → Value k) →
        ∀ {l u h} → Tree l u h → Tree l u h
  map f (leaf l<u)             = leaf l<u
  map f (node (k , v) l r bal) = node (k , f v) (map f l) (map f r) bal

  -- Converts the tree to an ordered list. Linear in the size of the
  -- tree.

  open DiffList

  toDiffList : ∀ {l u h} → Tree l u h → DiffList KV
  toDiffList (leaf _)       = []
  toDiffList (node k l r _) = toDiffList l ++ k ∷ toDiffList r

------------------------------------------------------------------------
-- Types and functions with hidden indices

data Tree : Set (k ⊔ v ⊔ ℓ) where
  tree : let open Extended-key in
         ∀ {h} → Indexed.Tree ⊥⁺ ⊤⁺ h → Tree

empty : Tree
empty = tree (Indexed.empty _)

singleton : (k : Key) → Value k → Tree
singleton k v = tree (Indexed.singleton k v _)

insert : (k : Key) → Value k → Tree → Tree
insert k v (tree t) = tree $ proj₂ $ Indexed.insert k v t _

insertWith : (k : Key) → Value k → (Value k → Value k → Value k) →
             Tree → Tree
insertWith k v f (tree t) = tree $ proj₂ $ Indexed.insertWith k v f t _

delete : Key → Tree → Tree
delete k (tree t) = tree $ proj₂ $ Indexed.delete k t

lookup : (k : Key) → Tree → Maybe (Value k)
lookup k (tree t) = Indexed.lookup k t

map : ({k : Key} → Value k → Value k) → Tree → Tree
map f (tree t) = tree $ Indexed.map f t

infix 4 _∈?_

_∈?_ : Key → Tree → Bool
k ∈? t = is-just (lookup k t)

headTail : Tree → Maybe (KV × Tree)
headTail (tree (Indexed.leaf _)) = nothing
headTail (tree {h = suc _} t)    with Indexed.headTail t
... | (k , _ , _ , t′) = just (k , tree (Indexed.castˡ _ t′))

initLast : Tree → Maybe (Tree × KV)
initLast (tree (Indexed.leaf _)) = nothing
initLast (tree {h = suc _} t)    with Indexed.initLast t
... | (k , _ , _ , t′) = just (tree (Indexed.castʳ t′ _) , k)

-- The input does not need to be ordered.

fromList : List KV → Tree
fromList = List.foldr (uncurry insert) empty

-- Returns an ordered list.

toList : Tree → List KV
toList (tree t) = DiffList.toList (Indexed.toDiffList t)

-- Naive implementations of union.

unionWith : (∀ {k} → Value k → Value k → Value k) →
            -- Left → right → result.
            Tree → Tree → Tree
unionWith f t₁ t₂ =
  List.foldr (λ { (k , v) → insertWith k v f }) t₂ (toList t₁)

-- Left-biased.

union : Tree → Tree → Tree
union = unionWith const

unionsWith : (∀ {k} → Value k → Value k → Value k) → List Tree → Tree
unionsWith f ts = List.foldr (unionWith f) empty ts

-- Left-biased.

unions : List Tree → Tree
unions = unionsWith const
