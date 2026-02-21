{-# OPTIONS --local-rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteBool where

module Foo (Bool : Set) (tt ff : Bool) (not : Bool → Bool)
           (@rew not-tt : not tt ≡ ff) (@rew not-ff : not ff ≡ tt)
           where
  test1 : not (not tt) ≡ tt
  test1 = refl

open import Agda.Builtin.Bool

not : Bool → Bool
not true  = false
not false = true

test2 : true ≡ true
test2 = Foo.test1 Bool true false not refl refl
