
module PreludeBool where
import AlonzoPrelude
open AlonzoPrelude

-- import Logic.Base

infixr 20 _||_
infixr 30 _&&_

data Bool : Set where
  false : Bool
  true  : Bool


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

-- open Logic.Base

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

