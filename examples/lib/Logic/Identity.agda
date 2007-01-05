
module Logic.Identity where

import Prelude
import Logic.Relations
import Logic.Equivalence

open Prelude
open Logic.Relations
open Logic.Equivalence using (Equivalence equiv)

data Identity (A : Set) : Set1 where
  identity :
    (_==_ : Rel A)    ->
    Reflexive _==_    ->
    Substitutive _==_ ->
    Identity A

module Projections where

  eq : {A : Set} -> Identity A -> Rel A
  eq (identity _==_ _ _) = _==_

  refl : {A : Set}(Id : Identity A) -> Reflexive (eq Id)
  refl (identity _ r _) = r

  subst : {A : Set}(Id : Identity A) -> Substitutive (eq Id)
  subst (identity _ _ s) = s

module Identity {A : Set}(Id : Identity A) where

  infix 40 _==_

  _==_ = Projections.eq Id
  
  refl : {x : A} -> x == x
  refl = Projections.refl Id _

  subst : (P : A -> Set){x y : A} -> x == y -> P x -> P y
  subst P = Projections.subst Id P _ _

  sym : {x y : A} -> x == y -> y == x
  sym {x}{y} xy = subst (\z -> z == x) xy refl

  trans : {x y z : A} -> x == y -> y == z -> x == z
  trans {x}{y}{z} xy yz = subst (\w -> x == w) yz xy

  cong : (f : A -> A){x y : A} -> x == y -> f x == f y
  cong f {x}{y} xy = subst (\z -> f x == f z) xy refl

  cong2 : (f : A -> A -> A){x y z w : A} -> x == z -> y == w -> f x y == f z w
  cong2 f {x}{y}{z}{w} xz yw =
    subst (\a -> f x y == f z a) yw $
    subst (\a -> f x y == f a y) xz refl

  Equiv : Equivalence A
  Equiv = equiv _==_ (\x -> refl {x}) (\x y -> sym {x}{y}) (\x y z -> trans {x}{y}{z})

