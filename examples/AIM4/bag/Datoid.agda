
module Datoid where

  import Equiv
  import Prelude

  open Equiv
  open Prelude

  data Datoid : Set1 where
    datoid : (a : Set) -> DecidableEquiv a -> Datoid

  El : Datoid -> Set
  El (datoid a _) = a

  datoidEq : (a : Datoid) -> DecidableEquiv (El a)
  datoidEq (datoid _ eq) = eq

  datoidRel : (a : Datoid) -> El a -> El a -> Set
  datoidRel d = rel' (datoidEq d)

  datoidDecRel :  (a : Datoid) -> (x y : El a)
               -> Either (datoidRel a x y) (Not (datoidRel a x y))
  datoidDecRel d = decRel (datoidEq d)

  dRefl : (a : Datoid) -> {x : El a} -> datoidRel a x x
  dRefl a = refl (datoidEq a)

  dSym : (a : Datoid) -> {x y : El a}
      -> datoidRel a x y -> datoidRel a y x
  dSym a = sym (datoidEq a)

  dTrans : (a : Datoid) -> {x y z : El a}
      -> datoidRel a x y -> datoidRel a y z -> datoidRel a x z
  dTrans a = trans (datoidEq a)

  data Respects (a : Datoid) (P : El a -> Set) : Set where
    respects : ((x y : El a) -> datoidRel a x y -> P x -> P y) -> Respects a P

  subst :  {a : Datoid} -> {P : El a -> Set} -> Respects a P
        -> (x y : El a) -> datoidRel a x y -> P x -> P y
  subst (respects f) = f

  pairDatoid : (a b : Datoid) -> Datoid
  pairDatoid a b = datoid (Pair (El a) (El b))
                          (pairEquiv (datoidEq a) (datoidEq b))

