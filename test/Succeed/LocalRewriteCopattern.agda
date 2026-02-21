{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- Based on #3812
module LocalRewriteCopattern where

record Box (A : Set) : Set where
  constructor box
  field unbox : A

open Box

module Test1 (A : Set) (r s : Box A) (@rew rew : r .unbox ≡ s .unbox) where

  ext : r ≡ s
  ext = refl

module Test2 (A : Set) (r : Nat → Box A) (@rew rew : r 0 .unbox ≡ r 1 .unbox) where

  ext : r 0 ≡ r 1
  ext = refl

postulate
  A : Set
  r s : Box A

module Test3 (@rew rew : r .unbox ≡ s .unbox) where

  ext : r ≡ s
  ext = refl
