
module Logic.Congruence where

import Prelude
import Logic.Relations
import Logic.Equivalence

open Prelude
open Logic.Relations
open Logic.Equivalence using    (Equivalence)
                       renaming (module Equivalence to Proj)

data Congruence (A : Set) : Set1 where
  congruence :
    (Eq : Equivalence A) ->
    Congruent (Proj._==_ Eq) ->
    Congruence A

module Projections where

  eq : {A : Set} -> Congruence A -> Rel A
  eq (congruence Eq _) = Proj._==_ Eq

  refl : {A : Set}(Cong : Congruence A) -> Reflexive (eq Cong)
  refl (congruence Eq _) = Proj.refl Eq

  sym : {A : Set}(Cong : Congruence A) -> Symmetric (eq Cong)
  sym (congruence Eq _) = Proj.sym Eq

  trans : {A : Set}(Cong : Congruence A) -> Transitive (eq Cong)
  trans (congruence Eq _) = Proj.trans Eq

  cong : {A : Set}(Cong : Congruence A) -> Congruent (eq Cong)
  cong (congruence _ c) = c

module Congruence {A : Set}(Cong : Congruence A) where

  _==_  = Projections.eq    Cong
  refl  = Projections.refl  Cong
  sym   = Projections.sym   Cong
  trans = Projections.trans Cong
  cong  = Projections.cong  Cong

  cong2 : (f : A -> A -> A)(a b c d : A) -> a == c -> b == d -> f a b == f c d
  cong2 f a b c d ac bd = trans _ _ _ rem1 rem2
    where
      rem1 : f a b == f a d
      rem1 = cong (f a) _ _ bd

      rem2 : f a d == f c d
      rem2 = cong (flip f d) _ _ ac

