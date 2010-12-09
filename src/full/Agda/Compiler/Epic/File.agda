{- An adaptation of Edwin Brady's paper Scrapping your inefficient engine ... -}
module File where

open import Unit
open import Bool
open import IO

data Ty : Set where
  TyUnit : Ty
  TyBool : Ty
  TyLift : Set -> Ty

interpTy : Ty -> Set
interpTy TyUnit     = Unit
interpTy TyBool     = Bool
interpTy (TyLift A) = A

data Imp : Ty -> Set where
  ACTION : ∀{a} -> IO a -> Imp (TyLift a)
  RETURN : ∀{a} -> interpTy a -> Imp a
  WHILE  :         Imp TyBool -> Imp TyUnit -> Imp TyUnit
  IF     : ∀{a} -> Bool -> Imp a -> Imp a -> Imp a
  BIND   : ∀{a b} -> Imp a -> (interpTy a -> Imp b) -> Imp b 

postulate
  while : ∀{a} -> IO Bool -> IO Unit -> IO Unit

{-# COMPILED_EPIC while (a : Unit, add : Any, body : Any, u : Unit) -> Any = while (add(u), body(u)) #-}

interp : ∀{a} -> Imp a -> IO (interpTy a)
interp (ACTION io) = io
interp (RETURN val) = return val
interp (WHILE add body) =
    while (interp add) (interp body)
interp (IF v thenp elsep) =
    if v then (interp thenp) else (interp elsep)
interp (BIND code k) =
    v <- interp code ,
    interp (k v)

prog : Imp TyUnit
prog = return unit

main = interp prog
