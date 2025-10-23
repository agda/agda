-- {-# OPTIONS -v interaction.case:90 #-}

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

-- Andreas, 2025-10-22, issue #8153
-- When introducing hidden arguments into the lhs,
-- bindings with unparsable generalized names should be skipped.

module Issue8153 where
  open import Agda.Primitive

  variable
    l : Level
    A : Set l

  id : A → A
  id = {!!}
    -- C-c C-x C-h C-c C-c RET

  -- WAS:
  --   id {A.l} {A} x = ?
  --
  -- Expected:
  --   id {A = A} x = ?
