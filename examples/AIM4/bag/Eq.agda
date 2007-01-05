
module Eq where

  import Prelude
  open Prelude

  abstract
    data _=^=_ {a : Set} (x y : a) : Set1 where
      leibniz : ((P : a -> Set) -> P x <-> P y) -> x =^= y

    leibnizSubst :  {a : Set} -> {x y : a}
                 -> x =^= y -> (P : a -> Set) -> P x -> P y
    leibnizSubst (leibniz f) P p = iffLeft (f P) p

    leibnizRefl : {a : Set} -> {x : a} -> x =^= x
    leibnizRefl = leibniz (\_ -> iff id id)

    leibnizSym : {a : Set} -> {x y : a} -> x =^= y -> y =^= x
    leibnizSym (leibniz f) =
      leibniz (\P -> iff (iffRight (f P)) (iffLeft (f P)))

