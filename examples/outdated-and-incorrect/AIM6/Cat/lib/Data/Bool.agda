
module Data.Bool where

import Logic.Base

infixr 10 _=>_!_
infix  5 !_
infix  12 otherwise_

infixr 20 _||_
infixr 30 _&&_

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

_&&_ : Bool -> Bool -> Bool
true  && x = x
false && _ = false

_||_ : Bool -> Bool -> Bool
true  || _ = true
false || x = x

not : Bool -> Bool
not true  = false
not false = true

open Logic.Base

IsTrue : Bool -> Set
IsTrue true  = True
IsTrue false = False

IsFalse : Bool -> Set
IsFalse x = IsTrue (not x)

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

if'_then_else_ : {A : Set} -> (x : Bool) -> (IsTrue x -> A) -> (IsFalse x -> A) -> A
if' true  then f else g = f tt
if' false then f else g = g tt

_=>_!_ : {A : Set} -> Bool -> A -> A -> A
_=>_!_ = if_then_else_

!_ : {A : Set} -> A -> A
! x = x

otherwise_ : {A : Set} -> A -> A
otherwise x = x

