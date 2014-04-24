{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS --sized-types #-}         -- no longer necessary
-- {-# OPTIONS --termination-depth=2 #-} -- no longer necessary
-- {-# OPTIONS -v term:10 #-}

module SizedBTree where

open import Common.Size

module Old where

  data BTree (A : Set) : {size : Size} → Set where
    leaf : {i : Size} → A → BTree A {↑ i}
    node : {i : Size} → BTree A {i} → BTree A {i} → BTree A {↑ i}

  map : ∀ {A B i} → (A → B) → BTree A {i} → BTree B {i}
  map f (leaf a) = leaf (f a)
  map f (node l r) = node (map f l) (map f r)

  -- deep matching

  deep : ∀ {i A} → BTree A {i} → A
  deep (leaf a) = a
  deep (node (leaf _) r) = deep r
  deep (node (node l r) _) = deep (node l r)

  -- nesting

  deep2 : ∀ {i A} → BTree A {i} → BTree A {i}
  deep2 (leaf a) = leaf a
  deep2 (node (leaf _) r) = r
  deep2 (node (node l r) t) with deep2 (deep2 (node l r))
  ... | leaf a = leaf a
  ... | node l2 r2 = deep2 (node l2 r2)

  -- OUTDATED: -- increasing the termination count does the job!

module New where

  data BTree (A : Set) {i : Size} :  Set where
    leaf : A → BTree A
    node : {i' : Size< i} → BTree A {i'} → BTree A {i'} → BTree A

  map : ∀ {A B i} → (A → B) → BTree A {i} → BTree B {i}
  map f (leaf a)   = leaf (f a)
  map f (node l r) = node (map f l) (map f r)

  -- deep matching

  deep : ∀ {i A} → BTree A {i} → A
  deep (leaf a)            = a
  deep (node (leaf _)   r) = deep r
  deep (node (node l r) _) = deep (node l r)

  -- nesting

  deep2 : ∀ {i A} → BTree A {i} → BTree A {i}
  deep2 (leaf a)            = leaf a
  deep2 (node (leaf _)   r) = r
  deep2 (node (node l r) _) with deep2 (deep2 (node l r))
  ... | leaf a     = leaf a
  ... | node l2 r2 = deep2 (node l2 r2)
