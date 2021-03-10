{-# OPTIONS --copatterns #-}

module SplitResult where

open import Common.Product

test : {A B : Set} (a : A) (b : B) → A × B
test a b = {!!}
-- expected:
-- proj₁ (test a b) = {!!}
-- proj₂ (test a b) = {!!}

testFun : {A B : Set} (a : A) (b : B) → A × B
testFun = {!!}
-- expected:
-- testFun a b = {!!}

record FunRec (A : Set) : Set where
  field funField : A → A
open FunRec

testFunRec : ∀{A} → FunRec A
testFunRec = {!!}
-- expected (since 2016-05-03):
-- funField testFunRec = {!!}

record ⊤ : Set where

issue4536 : ⊤
issue4536 = {!!}
-- expected
-- issue4536 = record{}
