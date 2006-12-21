
module DecidableOrder where

import Logic.Relations
import Logic.Leibniz

open Logic.Relations
open Logic.Leibniz

module Antisym = PolyEq _≡_
open Antisym, using (Antisymmetric)

data DecidableOrder (A : Set) : Set1 where
  decOrder :
    (_≤_ : Rel A)
    -> Reflexive _≤_
    -> Antisymmetric _≤_
    -> Transitive _≤_
    -> Total _≤_
    -> (forall x y -> Decidable (x ≤ y))
    -> DecidableOrder A

module Order {A : Set}(Ord : DecidableOrder A) where

  private
    leq : DecidableOrder A -> Rel A
    leq (decOrder l _ _ _ _ _) = l

    refl' : (Ord : DecidableOrder A) -> Reflexive (leq Ord)
    refl' (decOrder _ r _ _ _ _) = r

    antisym' : (Ord : DecidableOrder A) -> Antisymmetric (leq Ord)
    antisym' (decOrder _ _ a _ _ _) = a

    trans' : (Ord : DecidableOrder A) -> Transitive (leq Ord)
    trans' (decOrder _ _ _ t _ _) = t

    total' : (Ord : DecidableOrder A) -> Total (leq Ord)
    total' (decOrder _ _ _ _ t _) = t

    decide' : (Ord : DecidableOrder A) ->
	      forall x y -> Decidable (leq Ord x y)
    decide' (decOrder _ _ _ _ _ d) = d

  infix 100 _≤_

  _≤_     = leq Ord
  _≥_     = \x y -> y ≤ x
  refl    = refl' Ord
  antisym = antisym' Ord
  trans   = trans' Ord
  total   = total' Ord
  decide  = decide' Ord

-- We don't have η-equality on decidable orders so we define η-expansion:
η : {A : Set} -> DecidableOrder A -> DecidableOrder A
η Ord = decOrder _≤_ refl antisym trans total decide
  where
    module Ops = Order Ord
    open Ops

