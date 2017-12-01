------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed AVL trees
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_ ; refl)

module Data.AVL.Indexed
       {k r} (Key : Set k) {_<_ : Rel Key r}
       (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

open import Level using (_⊔_) -- ; Lift; lift)
open import Data.Nat.Base hiding (_<_; _⊔_; compare)
open import Data.Product hiding (map)
open import Data.Maybe hiding (map)
import Data.DifferenceList as DiffList
open import Function

open IsStrictTotalOrder isStrictTotalOrder
open import Data.AVL.Key Key isStrictTotalOrder public
open import Data.AVL.Height public

K&_ : ∀ {v} (Value : Key → Set v) → Set (k ⊔ v)
K& Value = Σ Key Value

-- The trees have three parameters/indices: a lower bound on the
-- keys, an upper bound, and a height.
--
-- (The bal argument is the balance factor.)

data Tree {v} (V : Key → Set v) (l u : Key⁺) : ℕ → Set (k ⊔ v ⊔ r) where
  leaf : (l<u : l <⁺ u) → Tree V l u 0
  node : ∀ {hˡ hʳ h}
         (k : K& V)
         (lk : Tree V l [ proj₁ k ] hˡ)
         (ku : Tree V [ proj₁ k ] u hʳ)
         (bal : hˡ ∼ hʳ ⊔ h) →
         Tree V l u (suc h)

module _ {v} {V : Key → Set v} where

  leaf-injective : ∀ {l u} {p q : l <⁺ u} → (Tree V l u 0 ∋ leaf p) ≡ leaf q → p ≡ q
  leaf-injective refl = refl

  node-injective-key : ∀ {hˡ hʳ h l u k₁ k₂}
    {lk₁ : Tree V l [ proj₁ k₁ ] hˡ} {lk₂ : Tree V l [ proj₁ k₂ ] hˡ}
    {ku₁ : Tree V [ proj₁ k₁ ] u hʳ} {ku₂ : Tree V [ proj₁ k₂ ] u hʳ}
    {bal₁ bal₂ : hˡ ∼ hʳ ⊔ h} → node k₁ lk₁ ku₁ bal₁ ≡ node k₂ lk₂ ku₂ bal₂ → k₁ ≡ k₂
  node-injective-key refl = refl

  node-injectiveˡ : ∀ {hˡ hʳ h l u k}
    {lk₁ : Tree V l [ proj₁ k ] hˡ} {lk₂ : Tree V l [ proj₁ k ] hˡ}
    {ku₁ : Tree V [ proj₁ k ] u hʳ} {ku₂ : Tree V [ proj₁ k ] u hʳ}
    {bal₁ bal₂ : hˡ ∼ hʳ ⊔ h} → node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → lk₁ ≡ lk₂
  node-injectiveˡ refl = refl

  node-injectiveʳ : ∀ {hˡ hʳ h l u k}
    {lk₁ : Tree V l [ proj₁ k ] hˡ} {lk₂ : Tree V l [ proj₁ k ] hˡ}
    {ku₁ : Tree V [ proj₁ k ] u hʳ} {ku₂ : Tree V [ proj₁ k ] u hʳ}
    {bal₁ bal₂ : hˡ ∼ hʳ ⊔ h} → node k lk₁ ku₁ bal₁ ≡ node k lk₂ ku₂ bal₂ → ku₁ ≡ ku₂
  node-injectiveʳ refl = refl

  node-injective-bal : ∀ {hˡ hʳ h l u k}
    {lk₁ : Tree V l [ proj₁ k ] hˡ} {lk₂ : Tree V l [ proj₁ k ] hˡ}
    {ku₁ : Tree V [ proj₁ k ] u hʳ} {ku₂ : Tree V [ proj₁ k ] u hʳ}
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

  castˡ : ∀ {l m u h} → l <⁺ m → Tree V m u h → Tree V l u h
  castˡ {l} l<m (leaf m<u)         = leaf (trans⁺ l l<m m<u)
  castˡ     l<m (node k mk ku bal) = node k (castˡ l<m mk) ku bal

  castʳ : ∀ {l m u h} → Tree V l m h → m <⁺ u → Tree V l u h
  castʳ {l} (leaf l<m)         m<u = leaf (trans⁺ l l<m m<u)
  castʳ     (node k lk km bal) m<u = node k lk (castʳ km m<u) bal

  -- Various constant-time functions which construct trees out of
  -- smaller pieces, sometimes using rotation.

  joinˡ⁺ : ∀ {l u hˡ hʳ h} →
           (k : K& V) →
           (∃ λ i → Tree V l [ proj₁ k ] (i ⊕ hˡ)) →
           Tree V [ proj₁ k ] u hʳ →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Tree V l u (i ⊕ (1 + h))
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
  joinˡ⁺ k₂ (## , t₁)               t₃ bal

  joinʳ⁺ : ∀ {l u hˡ hʳ h} →
           (k : K& V) →
           Tree V l [ proj₁ k ] hˡ →
           (∃ λ i → Tree V [ proj₁ k ] u (i ⊕ hʳ)) →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Tree V l u (i ⊕ (1 + h))
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
  joinʳ⁺ k₂ t₁ (## , t₃)               bal

  joinˡ⁻ : ∀ {l u} hˡ {hʳ h} →
           (k : K& V) →
           (∃ λ i → Tree V l [ proj₁ k ] pred[ i ⊕ hˡ ]) →
           Tree V [ proj₁ k ] u hʳ →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Tree V l u (i ⊕ h)
  joinˡ⁻ zero    k₂ (0# , t₁) t₃ bal = (1# , node k₂ t₁ t₃ bal)
  joinˡ⁻ zero    k₂ (1# , t₁) t₃ bal = (1# , node k₂ t₁ t₃ bal)
  joinˡ⁻ (suc _) k₂ (0# , t₁) t₃ ∼+  = joinʳ⁺ k₂ t₁ (1# , t₃) ∼+
  joinˡ⁻ (suc _) k₂ (0# , t₁) t₃ ∼0  = (1# , node k₂ t₁ t₃ ∼+)
  joinˡ⁻ (suc _) k₂ (0# , t₁) t₃ ∼-  = (0# , node k₂ t₁ t₃ ∼0)
  joinˡ⁻ (suc _) k₂ (1# , t₁) t₃ bal = (1# , node k₂ t₁ t₃ bal)
  joinˡ⁻ n       k₂ (## , t₁) t₃ bal

  joinʳ⁻ : ∀ {l u hˡ} hʳ {h} →
           (k : K& V) →
           Tree V l [ proj₁ k ] hˡ →
           (∃ λ i → Tree V [ proj₁ k ] u pred[ i ⊕ hʳ ]) →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Tree V l u (i ⊕ h)
  joinʳ⁻ zero    k₂ t₁ (0# , t₃) bal = (1# , node k₂ t₁ t₃ bal)
  joinʳ⁻ zero    k₂ t₁ (1# , t₃) bal = (1# , node k₂ t₁ t₃ bal)
  joinʳ⁻ (suc _) k₂ t₁ (0# , t₃) ∼-  = joinˡ⁺ k₂ (1# , t₁) t₃ ∼-
  joinʳ⁻ (suc _) k₂ t₁ (0# , t₃) ∼0  = (1# , node k₂ t₁ t₃ ∼-)
  joinʳ⁻ (suc _) k₂ t₁ (0# , t₃) ∼+  = (0# , node k₂ t₁ t₃ ∼0)
  joinʳ⁻ (suc _) k₂ t₁ (1# , t₃) bal = (1# , node k₂ t₁ t₃ bal)
  joinʳ⁻ n       k₂ t₁ (## , t₃) bal

  -- Extracts the smallest element from the tree, plus the rest.
  -- Logarithmic in the size of the tree.

  headTail : ∀ {l u h} → Tree V l u (1 + h) →
             ∃ λ (k : K& V) → l <⁺ [ proj₁ k ] ×
                            ∃ λ i → Tree V [ proj₁ k ] u (i ⊕ h)
  headTail (node k₁ (leaf l<k₁) t₂ ∼+) = (k₁ , l<k₁ , 0# , t₂)
  headTail (node k₁ (leaf l<k₁) t₂ ∼0) = (k₁ , l<k₁ , 0# , t₂)
  headTail (node {hˡ = suc _} k₃ t₁₂ t₄ bal) with headTail t₁₂
  ... | (k₁ , l<k₁ , t₂) = (k₁ , l<k₁ , joinˡ⁻ _ k₃ t₂ t₄ bal)

  -- Extracts the largest element from the tree, plus the rest.
  -- Logarithmic in the size of the tree.

  initLast : ∀ {l u h} → Tree V l u (1 + h) →
             ∃ λ (k : K& V) → [ proj₁ k ] <⁺ u ×
                            ∃ λ i → Tree V l [ proj₁ k ] (i ⊕ h)
  initLast (node k₂ t₁ (leaf k₂<u) ∼-) = (k₂ , k₂<u , (0# , t₁))
  initLast (node k₂ t₁ (leaf k₂<u) ∼0) = (k₂ , k₂<u , (0# , t₁))
  initLast (node {hʳ = suc _} k₂ t₁ t₃₄ bal) with initLast t₃₄
  ... | (k₄ , k₄<u , t₃) = (k₄ , k₄<u , joinʳ⁻ _ k₂ t₁ t₃ bal)

  -- Another joining function. Logarithmic in the size of either of
  -- the input trees (which need to have almost equal heights).

  join : ∀ {l m u hˡ hʳ h} →
         Tree V l m hˡ → Tree V m u hʳ → (bal : hˡ ∼ hʳ ⊔ h) →
         ∃ λ i → Tree V l u (i ⊕ h)
  join t₁ (leaf m<u) ∼0 = (0# , castʳ t₁ m<u)
  join t₁ (leaf m<u) ∼- = (0# , castʳ t₁ m<u)
  join {hʳ = suc _} t₁ t₂₃ bal with headTail t₂₃
  ... | (k₂ , m<k₂ , t₃) = joinʳ⁻ _ k₂ (castʳ t₁ m<k₂) t₃ bal

  -- An empty tree.

  empty : ∀ {l u} → l <⁺ u → Tree V l u 0
  empty = leaf

  -- A singleton tree.

  singleton : ∀ {l u} (k : Key) → V k → l < k < u → Tree V l u 1
  singleton k v (l<k , k<u) = node (k , v) (leaf l<k) (leaf k<u) ∼0

  -- Inserts a key into the tree, using a function to combine any
  -- existing value with the new value. Logarithmic in the size of the
  -- tree (assuming constant-time comparisons and a constant-time
  -- combining function).

  insertWith : ∀ {l u h} → (k : Key) → V k →
               (V k → V k → V k) →  -- New → old → result.
               Tree V l u h → l < k < u →
               ∃ λ i → Tree V l u (i ⊕ h)
  insertWith k v f (leaf l<u) l<k<u = (1# , singleton k v l<k<u)
  insertWith k v f (node (k′ , v′) lp pu bal) (l<k , k<u) with compare k k′
  ... | tri< k<k′ _ _ = joinˡ⁺ (k′ , v′) (insertWith k v f lp (l<k , k<k′)) pu bal
  ... | tri> _ _ k′<k = joinʳ⁺ (k′ , v′) lp (insertWith k v f pu (k′<k , k<u)) bal
  ... | tri≈ _ k≡k′ _ rewrite P.sym k≡k′ = (0# , node (k , f v v′) lp pu bal)

  -- Inserts a key into the tree. If the key already exists, then it
  -- is replaced. Logarithmic in the size of the tree (assuming
  -- constant-time comparisons).

  insert : ∀ {l u h} → (k : Key) → V k → Tree V l u h → l < k < u →
           ∃ λ i → Tree V l u (i ⊕ h)
  insert k v = insertWith k v const

  -- Deletes the key/value pair containing the given key, if any.
  -- Logarithmic in the size of the tree (assuming constant-time
  -- comparisons).

  delete : ∀ {l u h} → Key → Tree V l u h →
           ∃ λ i → Tree V l u pred[ i ⊕ h ]
  delete k (leaf l<u)         = (0# , leaf l<u)
  delete k (node p lp pu bal) with compare k (proj₁ p)
  ... | tri< _ _ _ = joinˡ⁻ _ p (delete k lp) pu bal
  ... | tri> _ _ _ = joinʳ⁻ _ p lp (delete k pu) bal
  ... | tri≈ _ _ _ = join lp pu bal

  -- Looks up a key. Logarithmic in the size of the tree (assuming
  -- constant-time comparisons).

  lookup : ∀ {l u h} → (k : Key) → Tree V l u h → Maybe (V k)
  lookup k (leaf _)                  = nothing
  lookup k (node (k′ , v) lk′ k′u _) with compare k k′
  ... | tri< _ _  _ = lookup k lk′
  ... | tri> _ _  _ = lookup k k′u
  ... | tri≈ _ eq _ rewrite eq = just v

  -- Converts the tree to an ordered list. Linear in the size of the
  -- tree.

  open DiffList

  toDiffList : ∀ {l u h} → Tree V l u h → DiffList (K& V)
  toDiffList (leaf _)       = []
  toDiffList (node k l r _) = toDiffList l ++ k ∷ toDiffList r

module _ {v w} {V : Key → Set v} {W : Key → Set w} where

  -- Maps a function over all values in the tree.

  map : (∀ {k} → V k → W k) → ∀ {l u h} → Tree V l u h → Tree W l u h
  map f (leaf l<u)             = leaf l<u
  map f (node (k , v) l r bal) = node (k , f v) (map f l) (map f r) bal

