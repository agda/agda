
module List where

import Bool
open Bool

infixr 15 _::_

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

module Eq {A : Set}(_=A=_ : A -> A -> Bool) where

  infix 10 _==_

  _==_ : List A -> List A -> Bool
  []      == []      = true
  x :: xs == y :: ys = (x =A= y) && xs == ys
  []      == _ :: _  = false
  _ :: _  == []      = false

module Subst {A : Set}(_=A=_ : A -> A -> Bool)
             (substA : {x y : A} -> (P : A -> Set) -> IsTrue (x =A= y) -> P x -> P y)
    where

  module EqA = Eq _=A=_
  open EqA

  subst : {xs ys : List A} -> (P : List A -> Set) -> IsTrue (xs == ys) -> P xs -> P ys
  subst {[]     } {_ :: _ } _ () _
  subst {_ :: _ } {[]     } _ () _
  subst {[]     } {[]     } P eq pxs = pxs
  subst {x :: xs} {y :: ys} P eq pxs =
    substA (\z -> P (z :: ys)) x==y (
      subst (\zs -> P (x :: zs)) xs==ys pxs
    )
    where
      x==y : IsTrue (x =A= y)
      x==y = isTrue&&₁ {x =A= y}{xs == ys} eq

      xs==ys : IsTrue (xs == ys)
      xs==ys = isTrue&&₂ {x =A= y}{xs == ys} eq

