-- Jesper, 2019-05-28: test case for #3812

{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

record Box (A : Set) : Set where
  constructor box
  field unbox : A

open Box

postulate
  A : Set
  r s : Box A
  rew₂ : r .unbox ≡ s .unbox

{-# REWRITE rew₂ #-}

Box-η : {x y : Box A} → x .unbox ≡ y .unbox → x ≡ y
Box-η refl = refl

-- WAS: `ext` reduces to `refl`, but giving `ext = refl` directly
-- leads to a type error.
ext : r ≡ s
ext = Box-η refl

ext' : r ≡ s
ext' = refl
