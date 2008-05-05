
module Lib.Eq where

open import Lib.Prelude
open import Lib.Nat renaming (_==_ to _=Nat=_)
open import Lib.Fin
open import Lib.List
open import Lib.Bool

-- Codes for types supporting equality

data EqU : Set where
  nat    : EqU
  bool   : EqU
  string : EqU
  unit   : EqU
  fin    : Nat -> EqU
  list   : EqU -> EqU
  pair   : EqU -> EqU -> EqU

El : EqU -> Set
El nat        = Nat
El bool       = Bool
El string     = String
El unit       = Unit
El (fin n)    = Fin n
El (list u)   = List (El u)
El (pair u v) = El u × El v

primitive primStringEquality : String -> String -> Bool

infix 30 _==_

_==_ : {u : EqU} -> El u -> El u -> Bool
_==_ {nat}    n         m           = n =Nat= m
_==_ {fin n}  i         j           = finEq i j
_==_ {bool}   false     y           = not y 
_==_ {bool}   true      y           = y
_==_ {string} x         y           = primStringEquality x y
_==_ {unit}   _         _           = true
_==_ {list u} []        []          = true
_==_ {list u} (x :: xs) (y :: ys)   = x == y && xs == ys
_==_ {list u} _     _               = false
_==_ {pair u v} (x₁ , y₁) (x₂ , y₂) = x₁ == x₂ && y₁ == y₂
