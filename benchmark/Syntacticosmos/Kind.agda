module Kind (Gnd : Set)(U : Set)(T : U -> Set) where

open import Basics
open import Pr
open import Nom

data Kind : Set where
  Ty    : Gnd -> Kind
  _|>_  : Kind -> Kind -> Kind
  Pi    : (u : U) -> (T u -> Kind) -> Kind

infixr 60 _|>_
