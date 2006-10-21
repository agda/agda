
module Logic.Equivalence where

import Logic.Relations
open   Logic.Relations

data Equivalence (A : Set) : Set1 where
  equiv :
    (_==_ : Rel A)
    -> Reflexive _==_
    -> Symmetric _==_
    -> Transitive _==_
    -> Equivalence A

module Equivalence {A : Set}(Eq : Equivalence A) where

  private
    eq    : Equivalence A -> Rel A
    eq (equiv _==_ _ _ _) = _==_

    refl' : (Eq : Equivalence A) -> Reflexive (eq Eq)
    refl' (equiv _ r _ _) = r

    sym' : (Eq : Equivalence A) -> Symmetric (eq Eq)
    sym' (equiv _ _ s _) = s

    trans' : (Eq : Equivalence A) -> Transitive (eq Eq)
    trans' (equiv _ _ _ t) = t

  _==_  = eq Eq
  refl  = refl' Eq
  sym   = sym' Eq
  trans = trans' Eq

