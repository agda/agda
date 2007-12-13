
module Bool where

import Logic
open Logic

data Bool : Set where
  false : Bool
  true  : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE true #-}

infixr 5 _&&_

_&&_ : Bool -> Bool -> Bool
true  && x = x
false && _ = false

not : Bool -> Bool
not true  = false
not false = true

IsTrue : Bool -> Set
IsTrue true  = True
IsTrue false = False

IsFalse : Bool -> Set
IsFalse x = IsTrue (not x)

module BoolEq where

  _==_ : Bool -> Bool -> Bool
  true  == x = x
  false == x = not x

  subst : {x y : Bool}(P : Bool -> Set) -> IsTrue (x == y) -> P x -> P y
  subst {true}{true}   _ _ px = px
  subst {false}{false} _ _ px = px
  subst {true}{false}  _ () _
  subst {false}{true}  _ () _

  isTrue== : {x : Bool} -> IsTrue x -> IsTrue (x == true)
  isTrue== {true} _ = tt
  isTrue== {false} ()

infix 1 if_then_else_

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

open BoolEq

if'_then_else_ : {A : Set} -> (x : Bool) -> (IsTrue x -> A) -> (IsFalse x -> A) -> A
if' true  then f else g = f tt
if' false then f else  g = g tt

isTrue&&₁ : {x y : Bool} -> IsTrue (x && y) -> IsTrue x
isTrue&&₁ {true} _ = tt
isTrue&&₁ {false} ()

isTrue&&₂ : {x y : Bool} -> IsTrue (x && y) -> IsTrue y
isTrue&&₂ {true} p = p
isTrue&&₂ {false} ()

