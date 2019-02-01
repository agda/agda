{-# OPTIONS --without-K #-}
module Common.Bool where

open import Agda.Builtin.Bool public

not : Bool -> Bool
not true  = false
not false = true

notnot : Bool -> Bool
notnot true  = not (not true)
notnot false = not (not false)

if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

