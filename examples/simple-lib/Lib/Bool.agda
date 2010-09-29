
module Lib.Bool where

open import Lib.Logic

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_DATA Bool Bool True False #-}

isTrue : Bool -> Set
isTrue true  = True
isTrue false = False

isFalse : Bool -> Set
isFalse true  = False
isFalse false = True

data Inspect (b : Bool) : Set where
  itsTrue  : .(isTrue b)  -> Inspect b
  itsFalse : .(isFalse b) -> Inspect b

inspect : (b : Bool) -> Inspect b
inspect true  = itsTrue _
inspect false = itsFalse _

infix 5 if_then_else_

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

not : Bool -> Bool
not true  = false
not false = true

infixr 25 _&&_
infixr 22 _||_

_&&_ : Bool -> Bool -> Bool
false && y = false
true  && y = y

_||_ : Bool -> Bool -> Bool
false || y = y
true  || y = true
