{-# OPTIONS --no-termination-check #-}

module Lambda where

module Prelude where

  data Bool : Set where
    true  : Bool
    false : Bool

  if_then_else_ : {A : Set} -> Bool -> A -> A -> A
  if true  then x else y = x
  if false then x else y = y

  _∧_ : Bool -> Bool -> Bool
  true  ∧ y = y
  false ∧ y = false

  _∨_ : Bool -> Bool -> Bool
  true  ∨ y = true
  false ∨ y = y

  ¬_ : Bool -> Bool
  ¬ true  = false
  ¬ false = true

  data List (A : Set) : Set where
    nil    : List A
    _::_ : A -> List A -> List A

  _++_ : {A : Set} -> List A -> List A -> List A
  nil      ++ ys = ys
  (x :: xs) ++ ys = x :: xs ++ ys

  filter : {A : Set} -> (A -> Bool) -> List A -> List A
  filter p  nil      = nil
  filter p (x :: xs) = if p x then x :: filter p xs else filter p xs

  postulate
    String : Set
    Int    : Set
    Char   : Set

  {-# BUILTIN BOOL    Bool   #-}
  {-# BUILTIN FALSE   false  #-}
  {-# BUILTIN TRUE    true   #-}
  {-# BUILTIN STRING  String #-}
  {-# BUILTIN INTEGER Int    #-}
  {-# BUILTIN CHAR    Char   #-}
  {-# BUILTIN LIST    List   #-}
  {-# BUILTIN NIL     nil    #-}
  {-# BUILTIN CONS    _::_    #-}

  primitive
    primStringEquality : String -> String -> Bool

  _==_ = primStringEquality

  infix 10 if_then_else_
  infixr 50 _::_ _++_
  infixl 5 _∨_
  infixl 7 _∧_
  infix 50 ¬_
  infix 15 _==_

open Prelude

Name : Set
Name = String

data Exp : Set where
  var  : Name -> Exp
  ƛ_⟶_ : Name -> Exp -> Exp
  _$_  : Exp -> Exp -> Exp

infixl 50 _$_
infix  20 ƛ_⟶_

infix 80 _[_/_]
infix 15 _∈_

_∈_ : Name -> List Name -> Bool
x ∈ y :: ys = x == y ∨ x ∈ ys
x ∈ nil    = false

-- Free variables
FV : Exp -> List Name
FV (var x)   = x :: nil
FV (s $ t)   = FV s ++ FV t
FV (ƛ x ⟶ t) = filter (\y -> ¬ (x == y)) (FV t)

-- Fresh names
fresh : Name -> Exp -> Name
fresh x e = fresh' (FV e)
  where
    fresh' : List Name -> Name
    fresh' xs = "z" -- TODO

-- Substitution
_[_/_] : Exp -> Exp -> Name -> Exp
var x     [ r / z ] = if x == z then r else var x
(s $ t)   [ r / z ] = s [ r / z ] $ t [ r / z ]
(ƛ x ⟶ t) [ r / z ] =
       if x == z   then ƛ x ⟶ t
  else if x ∈ FV r then ( let y : Name
                              y = fresh x r
                          in  ƛ y ⟶ t [ var y / x ] [ r / z ]
                        )
  else                  ƛ x ⟶ t [ r / z ]

