module Prelude.Bool where

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

not : Bool -> Bool
not true  = false
not false = true

notnot : Bool -> Bool
notnot true  = not (not true)
notnot false = not (not false)

infix 90 if_then_else_
infix 90 if'_then_else_


if_then_else_ : ∀{ P : Bool -> Set} -> (b : Bool) -> P true -> P false -> P b
if true  then a else b = a
if false then a else b = b

if'_then_else_ : ∀{ P : Set} -> (b : Bool) -> P -> P  -> P
if' true  then a else b = a
if' false then a else b = b