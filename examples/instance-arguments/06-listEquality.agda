-- {-# OPTIONS -v tc.constr.findInScope:50 #-}
module 06-listEquality where

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

data Bool : Set where
  true : Bool
  false : Bool

id : {A : Set} → A → A
id v = v

or : Bool → Bool → Bool
or true _ = true
or _ true = true
or false false = false

and : Bool → Bool → Bool
and false _ = false
and _ false = false
and true true = false

not : Bool → Bool
not true = false
not false = true

record Eq (A : Set) : Set where
  field eq : A → A → Bool

listEq : {A : Set} → Eq A → Eq (List A)
listEq {A} eqA = record { eq = eq' } where
  eq' : List A → List A → Bool
  eq' [] [] = true
  eq' (a ∷ as) (b ∷ bs) = and (Eq.eq eqA a b) (eq' as bs)
  eq' _ _ = false

primEqBool : Bool → Bool → Bool
primEqBool true = id
primEqBool false = not

eqBool : Eq Bool
eqBool = record { eq = primEqBool }

open Eq {{...}}

test = eq (true ∷ false ∷ true ∷ []) (true ∷ false ∷ [])
  where listBoolEq = listEq eqBool
