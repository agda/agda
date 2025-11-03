-- Andreas, 2025-11-03, issue #8182 reported and test by Szumi Xie

{-# OPTIONS --show-implicit #-}
{-# OPTIONS -v tc.generalize:10 #-}
{-# OPTIONS -v tc.rec:40 #-}
{-# OPTIONS -v tc.interaction:30 #-}

postulate
  P : (A : Set) → A → Set
  F : Set → Set
  g : (A : Set) → F A

variable G : Set

record R : Set₁ where
  h : G → P ? (g ?)
  h = ?

  field B : Set
