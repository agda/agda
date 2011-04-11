
module Equiv where

  import Prelude
  import Eq

  open Prelude
  open Eq

  data Equiv (a : Set) : Set1 where
    equiv :  (_==_  : a -> a -> Set)
          -> (refl  : (x : a) -> x == x)
          -> (sym   : (x y : a) -> x == y -> y == x)
          -> (trans : (x y z : a) -> x == y -> y == z -> x == z)
          -> Equiv a

  rel : {a : Set} -> Equiv a -> (a -> a -> Set)
  rel (equiv _==_ _ _ _) = _==_

  data Decidable {a : Set} (eq : a -> a -> Set) : Set where
    dec : ((x y : a) -> Either (eq x y) (Not (eq x y))) -> Decidable eq

  private
    boolFunctionsDecidable'
      : {a : Set}
      -> (f : a -> a -> Bool)
      -> (x y : a)
      -> (b : Bool)
      -> (b =^= f x y)
      -> Either (T' f x y) (Not (T' f x y))
    boolFunctionsDecidable' eq x y True  p = left (leibnizSubst p T unit)
    boolFunctionsDecidable' eq x y False p =
      right (not (\xy -> leibnizSubst (leibnizSym p) T xy))

  boolFunctionsDecidable
    : {a : Set} -> (f : a -> a -> Bool) -> Decidable (T' f)
  boolFunctionsDecidable f =
    dec (\x y -> boolFunctionsDecidable' f x y (f x y) leibnizRefl)

  data DecidableEquiv (a : Set) : Set1 where
    decEquiv : (eq : Equiv a) -> Decidable (rel eq) -> DecidableEquiv a

  rel' :  {a : Set} -> (eq : DecidableEquiv a) -> (a -> a -> Set)
  rel' (decEquiv eq _) = rel eq

  refl : {a : Set} -> (eq : DecidableEquiv a) -> {x : a} -> rel' eq x x
  refl (decEquiv (equiv _ refl' _ _) _) = refl' _

  sym : {a : Set} -> (eq : DecidableEquiv a) -> {x y : a}
      -> rel' eq x y -> rel' eq y x
  sym (decEquiv (equiv _ _ sym' _) _) = sym' _ _

  trans : {a : Set} -> (eq : DecidableEquiv a) -> {x y z : a}
      -> rel' eq x y -> rel' eq y z -> rel' eq x z
  trans (decEquiv (equiv _ _ _ trans') _) = trans' _ _ _

  decRel :  {a : Set} -> (eq : DecidableEquiv a) -> (x y : a)
         -> Either (rel' eq x y) (Not (rel' eq x y))
  decRel (decEquiv _ (dec f)) = f

  private

    decRelI :  {a : Set} -> (eq : a -> a -> Set) -> {x y : a}
             -> Either (eq x y) (Not (eq x y)) -> Bool
    decRelI _ (left _)  = True
    decRelI _ (right _) = False

  decRel' : {a : Set} -> DecidableEquiv a -> (a -> a -> Bool)
  decRel' eq x y = decRelI (rel' eq) (decRel eq x y)

  private
    pairEq :  {a b : Set} -> DecidableEquiv a -> DecidableEquiv b
           -> (p1 p2 : Pair a b) -> Set
    pairEq a b (pair x1 x2) (pair y1 y2) = Pair (rel' a x1 y1) (rel' b x2 y2)

    refl' :  {a b : Set} -> (da : DecidableEquiv a) -> (db : DecidableEquiv b)
          -> (x : Pair a b) -> pairEq da db x x
    refl' a b (pair x1 x2) = pair (refl a) (refl b)

    sym' :  {a b : Set} -> (da : DecidableEquiv a) -> (db : DecidableEquiv b)
         -> (x y : Pair a b) -> pairEq da db x y -> pairEq da db y x
    sym' a b (pair x1 x2) (pair y1 y2) (pair xy1 xy2) =
      pair (sym a xy1) (sym b xy2)

    trans'
      :  {a b : Set} -> (da : DecidableEquiv a) -> (db : DecidableEquiv b)
      -> (x y z : Pair a b)
      -> pairEq da db x y -> pairEq da db y z -> pairEq da db x z
    trans' a b (pair x1 x2) (pair y1 y2)
           (pair z1 z2) (pair xy1 xy2) (pair yz1 yz2) =
      pair (trans a xy1 yz1) (trans b xy2 yz2)

    dec'' :  {a b : Set} -> {da : DecidableEquiv a} -> {db : DecidableEquiv b}
          -> {x1 y1 : a} -> {x2 y2 : b}
          -> Either (rel' da x1 y1) (Not (rel' da x1 y1))
          -> Either (rel' db x2 y2) (Not (rel' db x2 y2))
          -> Either (pairEq da db (pair x1 x2) (pair y1 y2))
                    (Not (pairEq da db (pair x1 x2) (pair y1 y2)))
    dec'' (left xy1)         (left xy2)         = left (pair xy1 xy2)
    dec'' _                  (right (not nxy2)) =
      right (not (\xy -> nxy2 (snd xy)))
    dec'' (right (not nxy1)) (left _)           =
      right (not (\xy -> nxy1 (fst xy)))

    dec' :  {a b : Set} -> (da : DecidableEquiv a) -> (db : DecidableEquiv b)
         -> (x y : Pair a b) -> Either (pairEq da db x y) (Not (pairEq da db x y))
    dec' a b (pair x1 x2) (pair y1 y2) =
      dec'' {_} {_} {a} {b} (decRel a x1 y1) (decRel b x2 y2)

  pairEquiv
    :  {a b : Set} -> DecidableEquiv a -> DecidableEquiv b
    -> DecidableEquiv (Pair a b)
  pairEquiv a b = decEquiv (equiv (pairEq a b)
                                  (refl' a b) (sym' a b) (trans' a b))
                           (dec (dec' a b))

