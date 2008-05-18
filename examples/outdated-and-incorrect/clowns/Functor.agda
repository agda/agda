{-# OPTIONS --no-positivity-check #-}

module Functor where

import Sets

open Sets

infixr 40 _+_ _+₂_
infixr 60 _×_ _×₂_
infix  80 _[_]

data U : Set1 where
  K   : Set -> U
  Id  : U
  _+_ : U -> U -> U
  _×_ : U -> U -> U

data U₂ : Set1 where
  K₂   : (A : Set) -> U₂
  ↖    : U -> U₂
  ↗    : U -> U₂
  _+₂_ : U₂ -> U₂ -> U₂
  _×₂_ : U₂ -> U₂ -> U₂

-- Functor composition
_[_] : U -> U -> U
K A	[ H ] = K A
Id	[ H ] = H
(F + G) [ H ] = F [ H ] + G [ H ]
(F × G) [ H ] = F [ H ] × G [ H ]

module Semantics where

  -- The semantic of a functor
  ⟦_⟧ : U -> Set -> Set
  ⟦ K A	  ⟧ X = A
  ⟦ Id	  ⟧ X = X
  ⟦ F + G ⟧ X = ⟦ F ⟧ X [+] ⟦ G ⟧ X
  ⟦ F × G ⟧ X = ⟦ F ⟧ X [×] ⟦ G ⟧ X

  ⟦_⟧₂ : (F : U₂) -> Set -> Set -> Set
  ⟦ K₂ A   ⟧₂ C J = A
  ⟦ ↖ F	   ⟧₂ C J = ⟦ F ⟧ C
  ⟦ ↗ F	   ⟧₂ C J = ⟦ F ⟧ J
  ⟦ F +₂ G ⟧₂ C J = ⟦ F ⟧₂ C J [+] ⟦ G ⟧₂ C J
  ⟦ F ×₂ G ⟧₂ C J = ⟦ F ⟧₂ C J [×] ⟦ G ⟧₂ C J

module Recursive where

  -- Fixed points (we need to turn off positivity checking since we can't see
  -- that ⟦ F ⟧ is covariant).

  open Semantics

  data μ (F : U) : Set where
    inn : ⟦ F ⟧ (μ F) -> μ F

  out : {F : U} -> μ F -> ⟦ F ⟧ (μ F)
  out (inn f) = f

