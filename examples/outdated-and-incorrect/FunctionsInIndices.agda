module FunctionsInIndices where

open import Prelude
open import Eq

data Tree (a : Set) : ℕ -> Set where
  leaf : a -> Tree a 1
  node : forall n₁ n₂ -> Tree a n₁ -> Tree a n₂ -> Tree a (n₁ + n₂)

-- This does not work:

-- leftmost : forall {a} n -> Tree a (suc n) -> a
-- leftmost .0         (leaf x)                     = x
-- leftmost .n₂        (node zero     (suc n₂) l r) = leftmost l
-- leftmost .(n₁ + n₂) (node (suc n₁) n₂       l r) = leftmost l

module Workaround1 where

  private

    T : Set -> ℕ -> Set
    T a zero    = ⊤
    T a (suc n) = a

    leftmost' : forall {a n} -> Tree a n -> T a n
    leftmost' (leaf x)                     = x
    leftmost' (node zero     zero     l r) = tt
    leftmost' (node zero     (suc n₂) l r) = leftmost' r
    leftmost' (node (suc n₁) n₂       l r) = leftmost' l

  leftmost : forall {a n} -> Tree a (suc n) -> a
  leftmost = leftmost'

module Workaround2 where

  private

    leftmost' : forall {a n m} -> Tree a m -> m ≡ suc n -> a
    leftmost' (leaf x)                     _  = x
    leftmost' (node zero     (suc n₂) l r) _  = leftmost' r refl
    leftmost' (node (suc n₁) n₂       l r) _  = leftmost' l refl

  leftmost : forall {a n} -> Tree a (suc n) -> a
  leftmost t = leftmost' t refl
