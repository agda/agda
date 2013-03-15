-- Andreas and James, Nov 2011 and Oct 2012
-- function with flexible arity
-- {-# OPTIONS --no-coverage-check #-}
-- {-# OPTIONS -v tc.lhs:20 -v tc.cover.top:20 #-}
module FlexibleInterpreter where

open import Common.Prelude
open import Common.MAlonzo hiding (main)
open import Common.Equality

data Ty : Set where
  nat : Ty
  arr : Ty -> Ty -> Ty

data Exp : Ty -> Set where
  zero : Exp nat
  suc  : Exp (arr nat nat)
  pred : Exp (arr nat nat)
  app  : {a b : Ty} -> Exp (arr a b) -> Exp a -> Exp b

Sem : Ty -> Set
Sem nat = Nat
Sem (arr a b) = Sem a -> Sem b

module Flex where
  -- Haskell does not seem to handle this

  eval' : (a : Ty) -> Exp a -> Sem a
  eval' ._ zero = zero
  eval' ._ suc  = suc
  eval' b (app f e) = eval' _ f (eval' _ e)
  eval' .(arr nat nat) pred zero = zero
  eval' ._ pred (suc n) = n

  eval : {a : Ty} -> Exp a -> Sem a
  eval zero         = zero
  eval suc          = suc
  eval pred zero    = zero
  eval pred (suc n) = n
  eval (app f e)    = eval f (eval e)

  testEvalSuc : ∀ {n} → eval suc n ≡ suc n
  testEvalSuc = refl

  testEvalPredZero : eval pred zero ≡ zero
  testEvalPredZero = refl

  testEvalPredSuc : ∀ {n} → eval pred (suc n) ≡ n
  testEvalPredSuc = refl

module Rigid where
  -- This executes fine

  eval : {a : Ty} -> Exp a -> Sem a
  eval zero      = zero
  eval suc       = suc
  eval pred      = λ { zero    -> zero
                     ; (suc n) -> n
                     }
  eval (app f e) = eval f (eval e)

open Flex

expr = (app pred (app suc (app suc zero)))
test = eval expr
main = mainPrintNat test
-- should print 1
