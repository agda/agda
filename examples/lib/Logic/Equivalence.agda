
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

module Projections where

  eq : {A : Set} -> Equivalence A -> Rel A
  eq (equiv _==_ _ _ _) = _==_

  refl : {A : Set}(Eq : Equivalence A) -> Reflexive (eq Eq)
  refl (equiv _ r _ _) = r

  sym : {A : Set}(Eq : Equivalence A) -> Symmetric (eq Eq)
  sym (equiv _ _ s _) = s

  trans : {A : Set}(Eq : Equivalence A) -> Transitive (eq Eq)
  trans (equiv _ _ _ t) = t

module Equivalence {A : Set}(Eq : Equivalence A) where

  _==_  = Projections.eq Eq
  refl  = Projections.refl Eq
  sym   = Projections.sym Eq
  trans = Projections.trans Eq

