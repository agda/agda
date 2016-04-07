-- Andreas and James, Nov 2011 and Oct 2012
-- function with flexible arity
-- {-# OPTIONS -v tc.cover:20 #-}
module FlexibleInterpreter where

open import Common.Equality
open import Common.IO
open import Common.Nat renaming (zero to Z; suc to S) hiding (pred)

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
  eval' ._ zero = Z
  eval' ._ suc  = S
  eval' b (app f e) = eval' _ f (eval' _ e)
  eval' .(arr nat nat) pred Z = Z
  eval' ._ pred (S n) = n

  eval : {a : Ty} -> Exp a -> Sem a
  eval zero         = Z
  eval suc          = S
  eval pred Z       = Z
  eval pred (S n)   = n
  eval (app f e)    = eval f (eval e)

  testEvalSuc : ∀ {n} → eval suc n ≡ S n
  testEvalSuc = refl

  testEvalPredZero : eval pred Z ≡ Z
  testEvalPredZero = refl

  testEvalPredSuc : ∀ {n} → eval pred (S n) ≡ n
  testEvalPredSuc = refl

module Rigid where
  -- This executes fine

  eval : {a : Ty} -> Exp a -> Sem a
  eval zero      = Z
  eval suc       = S
  eval pred      = λ { Z    -> Z
                     ; (S n) -> n
                     }
  eval (app f e) = eval f (eval e)

open Flex

expr = (app pred (app suc (app suc zero)))
test = eval expr
main = printNat test
-- should print 1
