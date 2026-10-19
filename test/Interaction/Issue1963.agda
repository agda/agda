-- Andreas, May-July 2016, implementing postfix projections

{-# OPTIONS --postfix-projections #-}

open import Common.Product
open import Common.Bool

pair : ∀{A : Set}(a : A) → A × A
pair a = {!!} -- C-c C-c here outputs postfix projections

record BoolFun : Set where
  field out : Bool → Bool
open BoolFun

neg : BoolFun
neg .out x = {!x!} -- splitting here should preserve postfix proj

neg2 : BoolFun
out neg2 x = {!x!} -- splitting here should preserve prefix proj

module ExtendedLambda where

  neg3 : BoolFun
  neg3 = λ{ .out → {!!} }

  pair2 : ∀{A : Set}(a : A) → A × A
  pair2 = λ{ a → {!!} }

  neg4 : BoolFun
  neg4 = λ{ .out b → {!b!} }

-- DOES NOT WORK DUE TO ISSUE #2020

-- module LambdaWhere where

--   neg3 : BoolFun
--   neg3 = λ where
--     .out → {!!} -- splitting on result here crashes

--   pair2 : ∀{A : Set}(a : A) → A × A
--   pair2 = λ where
--     a → {!!}

--   extlam-where : Bool → Bool
--   extlam-where = λ where
--     b → {!b!}

-- -- extlam : Bool → Bool
-- -- extlam = λ
-- --   { b → {!b!}
-- --   }
