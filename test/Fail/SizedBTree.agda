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

  -- Jesper 2015-12-18: The new unifier requires the size argument of the first
  -- deep2 to be given explicitly. This is because otherwise the unifier gets
  -- stuck on an equation [↑ i₁ =?= _i_46 {i} {A} l r t]. It's not clear whether
  -- it is safe to instantiate the meta to [↑ _] here.

  -- Jesper 2019-05-21: This no longer passes the termination check
  -- since the removal of with-inlining.
  deep2 : ∀ {i A} → BTree A {i} → BTree A {i}
  deep2 (leaf a) = leaf a
  deep2 (node (leaf _) r) = r
  deep2 (node (node {i} l r) t) with deep2 {↑ i} (deep2 (node l r))
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
