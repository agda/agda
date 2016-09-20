-- 2014-02-08 Andreas
-- Eta-equality for records that are recursive via some data type

-- {-# OPTIONS -v tc.pos.record:10 #-}

module _ where

open import Common.Equality

module Nested where

  data List (A : Set) : Set where
    []  : List A
    _∷_ : (x : A)(xs : List A) → List A

  record Tree (A : Set) : Set where
    inductive
    constructor tree
    field
      elem     : A
      subtrees : List (Tree A)
  open Tree

  test : ∀ {A} (t : Tree A) → t ≡ tree (elem t) (subtrees t)
  test t = refl

  -- we should have eta for Tree!

module Mutual where

  mutual
    data TreeList (A : Set) : Set where
      []  : TreeList A
      _∷_ : (x : Tree A)(xs : TreeList A) → TreeList A

    record Tree (A : Set) : Set where
      inductive
      constructor tree
      field
        elem     : A
        subtrees : TreeList A
  open Tree

  test : ∀ {A} (t : Tree A) → t ≡ tree (elem t) (subtrees t)
  test t = refl
