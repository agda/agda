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
    l   : Level
    A B : Set l
    x   : A

  -- Intermittent bug after #8154
  mix : (y : A) (R : B → {C : Set} → C → Set) (p : R x y) → R x y
  mix = {!!}

  -- WAS after #8154:
  --   mix {B = B} y R p = {!!}
  --
  -- Expected:
  --   mix y R p = {!!}

  id : A → A
  id = {!!}
    -- C-c C-x C-h C-c C-c RET

  -- WAS:
  --   id {A.l} {A} x = ?
  --
  -- Expected:
  --   id {A = A} x = ?

-- Andreas, 2025-10-25, issue #8157
-- Splitting makes instance clauses vanish.

module Issue8157 where
  open import Agda.Builtin.Nat

  postulate
    A : Set
    instance a : A

  record R : Set where
    field {{i}} : A

  issue8157 : Nat → R
  issue8157 n .R.i = {!n!}  -- C-c -C-c n

  -- Splitting here makes the clause disappear as a whole.
  --
  -- Expected:  Splitting succeeds ordinarily and produces:
  --    test zero    .R.i = ?
  --    test (suc n) .R.i = ?
