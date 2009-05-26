------------------------------------------------------------------------
-- Directed acyclic multigraphs
------------------------------------------------------------------------

-- A representation of DAGs, based on the idea underlying Martin
-- Erwig's FGL. Note that this representation does not aim to be
-- efficient.

module Data.Graph.Acyclic where

open import Data.Nat as Nat using (ℕ; zero; suc; _<′_)
import Data.Nat.Properties as Nat
open import Data.Fin as Fin
  using (Fin; Fin′; zero; suc; #_; toℕ) renaming (_ℕ-ℕ_ to _-_)
open import Data.Fin.Props as FP using (_≟_)
open import Data.Product as Prod using (∃; _×_; _,_)
open import Data.Maybe
open import Data.Function
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Induction.Nat

------------------------------------------------------------------------
-- A lemma

private

  lemma : ∀ n (i : Fin n) → n - suc i <′ n
  lemma zero    ()
  lemma (suc n) i  = Nat.≤⇒≤′ $ Nat.s≤s $ FP.nℕ-ℕi≤n n i

------------------------------------------------------------------------
-- Node contexts

record Context (Node Edge : Set) (n : ℕ) : Set where
  field
    label      : Node
    successors : List (Edge × Fin n)

open Context public

context : ∀ {Node Edge n} →
          Node → List (Edge × Fin n) → Context Node Edge n
context l ss = record { label = l; successors = ss }

-- Map for contexts.

cmap : ∀ {N₁ N₂ E₁ E₂ n} →
       (N₁ → N₂) → (List (E₁ × Fin n) → List (E₂ × Fin n)) →
       Context N₁ E₁ n → Context N₂ E₂ n
cmap f g c = context (f (label c)) (g (successors c))

------------------------------------------------------------------------
-- Graphs

infixr 3 _&_

-- The DAGs are indexed on the number of nodes.

data Graph (Node Edge : Set) : ℕ → Set where
  ∅   : Graph Node Edge 0
  _&_ : ∀ {n} (c : Context Node Edge n) (g : Graph Node Edge n) →
        Graph Node Edge (suc n)

private

  example : Graph ℕ ℕ 5
  example = context 0 [] &
            context 1 ((10 , # 1) ∷ (11 , # 1) ∷ []) &
            context 2 ((12 , # 0) ∷ []) &
            context 3 [] &
            context 4 [] &
            ∅

------------------------------------------------------------------------
-- Higher-order functions

-- "Fold right".

foldr : ∀ {N E m} (T : ℕ → Set) →
        (∀ {n} → Context N E n → T n → T (suc n)) →
        T 0 →
        Graph N E m → T m
foldr T _∙_ x ∅       = x
foldr T _∙_ x (c & g) = c ∙ foldr T _∙_ x g

-- "Fold left".

foldl : ∀ {N E n} (T : ℕ → Set) →
        ((i : Fin n) → T (toℕ i) → Context N E (n - suc i) →
         T (suc (toℕ i))) →
        T 0 →
        Graph N E n → T n
foldl T f x ∅       = x
foldl T f x (c & g) =
  foldl (λ n → T (suc n)) (λ i → f (suc i)) (f zero x c) g

-- Maps over node contexts.

map : ∀ {N₁ N₂ E₁ E₂ n} →
      (∀ {n} → Context N₁ E₁ n → Context N₂ E₂ n) →
      Graph N₁ E₁ n → Graph N₂ E₂ n
map f = foldr _ (λ c g → f c & g) ∅

-- Maps over node labels.

nmap : ∀ {N₁ N₂ E n} → (N₁ → N₂) → Graph N₁ E n → Graph N₂ E n
nmap f = map (cmap f id)

-- Maps over edge labels.

emap : ∀ {N E₁ E₂ n} → (E₁ → E₂) → Graph N E₁ n → Graph N E₂ n
emap f = map (cmap id (List.map (Prod.map f id)))

-- Zips two graphs with the same number of nodes. Note that one of the
-- graphs has a type which restricts it to be completely disconnected.

zipWith : ∀ {N₁ N₂ N E n} → (N₁ → N₂ → N) →
          Graph N₁ ⊥ n → Graph N₂ E n → Graph N E n
zipWith _∙_ ∅         ∅         = ∅
zipWith _∙_ (c₁ & g₁) (c₂ & g₂) =
  context (label c₁ ∙ label c₂) (successors c₂) & zipWith _∙_ g₁ g₂

------------------------------------------------------------------------
-- Specific graphs

-- A completeley disconnected graph.

disconnected : ∀ n → Graph ⊤ ⊥ n
disconnected zero    = ∅
disconnected (suc n) = context tt [] & disconnected n

-- A complete graph.

complete : ∀ n → Graph ⊤ ⊤ n
complete zero    = ∅
complete (suc n) =
  context tt (List.map (_,_ tt) $ Vec.toList (Vec.allFin n)) &
  complete n

------------------------------------------------------------------------
-- Queries

-- The top-most context.

head : ∀ {N E n} → Graph N E (suc n) → Context N E n
head (c & g) = c

-- The remaining graph.

tail : ∀ {N E n} → Graph N E (suc n) → Graph N E n
tail (c & g) = g

-- Finds the context and remaining graph corresponding to a given node
-- index.

_[_] : ∀ {N E n} →
       Graph N E n → (i : Fin n) → Graph N E (suc (n - suc i))
∅       [ () ]
(c & g) [ zero ]  = c & g
(c & g) [ suc i ] = g [ i ]

-- The nodes of the graph (node number relative to "topmost" node ×
-- node label).

nodes : ∀ {N E n} → Graph N E n → Vec (Fin n × N) n
nodes {N} = Vec.zip (Vec.allFin _) ∘
            foldr (Vec N) (λ c ns → label c ∷ ns) []

private

  test-nodes : nodes example ≡ (# 0 , 0) ∷ (# 1 , 1) ∷ (# 2 , 2) ∷
                               (# 3 , 3) ∷ (# 4 , 4) ∷ []
  test-nodes = refl

-- Topological sort. Gives a vector where earlier nodes are never
-- successors of later nodes.

topSort : ∀ {N E n} → Graph N E n → Vec (Fin n × N) n
topSort = nodes

-- The edges of the graph (predecessor × edge label × successor).
--
-- The predecessor is a node number relative to the "topmost" node in
-- the graph, and the successor is a node number relative to the
-- predecessor.

edges : ∀ {E N n} → Graph N E n → List (∃ λ i → E × Fin (n - suc i))
edges {E} {N} {n} =
  foldl (λ _ → List (∃ λ i → E × Fin (n - suc i)))
        (λ i es c → List._++_ es (List.map (_,_ i) (successors c)))
        []

private

  test-edges : edges example ≡ (# 1 , 10 , # 1) ∷ (# 1 , 11 , # 1) ∷
                               (# 2 , 12 , # 0) ∷ []
  test-edges = refl

-- The successors of a given node i (edge label × node number relative
-- to i).

sucs : ∀ {E N n} →
       Graph N E n → (i : Fin n) → List (E × Fin (n - suc i))
sucs g i = successors $ head $ g [ i ]

private

  test-sucs : sucs example (# 1) ≡ (10 , # 1) ∷ (11 , # 1) ∷ []
  test-sucs = refl

-- The predecessors of a given node i (node number relative to i ×
-- edge label).

preds : ∀ {E N n} → Graph N E n → (i : Fin n) → List (Fin′ i × E)
preds g       zero    = []
preds (c & g) (suc i) =
  List._++_ (List.gfilter (p i) $ successors c)
            (List.map (Prod.map suc id) $ preds g i)
  where
  p : ∀ {E n} (i : Fin n) → E × Fin n → Maybe (Fin′ (suc i) × E)
  p i (e , j)  with i ≟ j
  p i (e , .i) | yes refl = just (zero , e)
  p i (e , j)  | no _     = nothing

private

  test-preds : preds example (# 3) ≡
               (# 1 , 10) ∷ (# 1 , 11) ∷ (# 2 , 12) ∷ []
  test-preds = refl

------------------------------------------------------------------------
-- Operations

-- Weakens a node label.

weaken : ∀ {n} {i : Fin n} → Fin (n - suc i) → Fin n
weaken {n} {i} j = Fin.inject≤ j (FP.nℕ-ℕi≤n n (suc i))

-- Labels each node with its node number.

number : ∀ {N E n} → Graph N E n → Graph (Fin n × N) E n
number {N} {E} =
  foldr (λ n → Graph (Fin n × N) E n)
        (λ c g → cmap (_,_ zero) id c & nmap (Prod.map suc id) g)
        ∅

private

  test-number : number example ≡
                (context (# 0 , 0) [] &
                 context (# 1 , 1) ((10 , # 1) ∷ (11 , # 1) ∷ []) &
                 context (# 2 , 2) ((12 , # 0) ∷ []) &
                 context (# 3 , 3) [] &
                 context (# 4 , 4) [] &
                 ∅)
  test-number = refl

-- Reverses all the edges in the graph.

reverse : ∀ {N E n} → Graph N E n → Graph N E n
reverse {N} {E} g =
  foldl (Graph N E)
        (λ i g' c →
           context (label c)
                   (List.map (Prod.swap ∘ Prod.map FP.reverse id) $
                             preds g i)
           & g')
        ∅ g

private

  test-reverse : reverse (reverse example) ≡ example
  test-reverse = refl

------------------------------------------------------------------------
-- Views

-- Expands the subgraph induced by a given node into a tree (thus
-- losing all sharing).

data Tree N E : Set where
  node : (label : N) (successors : List (E × Tree N E)) → Tree N E

toTree : ∀ {N E n} → Graph N E n → Fin n → Tree N E
toTree {N} {E} g i = <-rec Pred expand _ (g [ i ])
  where
  Pred = λ n → Graph N E (suc n) → Tree N E

  expand : (n : ℕ) → <-Rec Pred n → Pred n
  expand n rec (c & g) =
    node (label c)
         (List.map
            (Prod.map id (λ i → rec (n - suc i) (lemma n i) (g [ i ])))
            (successors c))

-- Performs the toTree expansion once for each node.

toForest : ∀ {N E n} → Graph N E n → Vec (Tree N E) n
toForest g = Vec.map (toTree g) (Vec.allFin _)

private

  test-toForest : toForest example ≡
                    let n3 = node 3 [] in
                    node 0 [] ∷
                    node 1 ((10 , n3) ∷ (11 , n3) ∷ []) ∷
                    node 2 ((12 , n3) ∷ []) ∷
                    node 3 [] ∷
                    node 4 [] ∷
                    []
  test-toForest = refl
