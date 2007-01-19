
module MinMax where

import Prelude
import Logic.Base
import Logic.Relations
import Logic.Leibniz
import Logic.ChainReasoning
import DecidableOrder

open Prelude
open Logic.Base
open Logic.Relations
open Logic.Leibniz
open DecidableOrder

module Min {A : Set}(Ord : DecidableOrder A) where

  private
    module Ops = Order Ord
    open Ops

  private
    minAux : (x y : A) -> x ≤ y \/ ¬ x ≤ y -> A
    minAux x y (\/-IL _) = x
    minAux x y (\/-IR _) = y

  min : A -> A -> A
  min a b = minAux a b (decide a b)

  case-min : (P : A -> Set)(x y : A) ->
            (x ≤ y -> P x) ->
            (y ≤ x -> P y) -> P (min x y)
  case-min P x y ifx ify =
      elimD-\/ (\z -> P (minAux x y z)) ifx (more (total x y)) (decide x y)
    where
      more : x ≤ y \/ y ≤ x -> ¬ x ≤ y -> P y
      more (\/-IL xy) not-xy = elim-False (not-xy xy)
      more (\/-IR yx) _      = ify yx

  min-glb : forall x y z -> z ≤ x -> z ≤ y -> z ≤ min x y
  min-glb x y z zx zy = case-min (\w -> z ≤ w) x y (\_ -> zx) (\_ -> zy)

  min-left : forall x y -> min x y ≤ x
  min-left x y = case-min (\z -> z ≤ x) x y (\_ -> refl _) id

  min-right : forall x y -> min x y ≤ y
  min-right x y = case-min (\z -> z ≤ y) x y id (\_ -> refl _)

  min-sym : forall x y -> min x y ≡ min y x
  min-sym x y = antisym _ _ (lem x y) (lem y x)
    where
      lem : forall a b -> min a b ≤ min b a
      lem a b = case-min (\c -> min a b ≤ c) b a
                         (\_ -> min-right _ _)
                         (\_ -> min-left _ _)

Dual : {A : Set} -> DecidableOrder A -> DecidableOrder A
Dual Ord = decOrder _≥_ refl' antisym' trans' total' dec'
  where
    module Ops = Order Ord
    open Ops
    refl'    = refl
    antisym' = \x y xy yx   -> antisym _ _ yx xy
    trans'   = \x y z xy yz -> trans _ _ _ yz xy
    total'   = \x y         -> total _ _
    dec'     = \x y         -> decide _ _

module Max {A : Set}(Ord : DecidableOrder A)
      = Min (Dual Ord) renaming
              ( min      to max
              ; case-min  to case-max
              ; min-glb   to max-lub
              ; min-sym   to max-sym
              ; min-right to max-right
              ; min-left  to max-left
              )

module MinMax {A : Set}(Ord : DecidableOrder A) where

  private
    module MinOrd = Min Ord
    module MaxOrd = Max Ord

  open MinOrd public
  open MaxOrd public

module DistributivityA {A : Set}(Ord : DecidableOrder A) where

  private
    module MinMaxOrd = MinMax Ord
    module Ops       = Order Ord

    open MinMaxOrd
    open Ops

  min-max-distr : forall x y z -> min x (max y z) ≡ max (min x y) (min x z)
  min-max-distr x y z = antisym _ _ left right
    where
      module Chain = Logic.ChainReasoning.Mono.Homogenous _≤_ refl trans
      open Chain

      left : min x (max y z) ≤ max (min x y) (min x z)
      left = case-max (\w -> min x w ≤ max (min x y) (min x z)) y z
                      (\_ -> max-left _ _)
                      (\_ -> max-right _ _)

      right : max (min x y) (min x z) ≤ min x (max y z)
      right = case-max (\w -> w ≤ min x (max y z)) (min x y) (min x z)
                       (\_ -> case-max (\w -> min x y ≤ min x w) y z
                                (\_  -> refl _)
                                (\yz -> min-glb x z _ (min-left x y)
                                          ( chain>
                                            min x y === y  by  min-right x y
                                                    === z  by  yz
                                          )
                                )
                       )
                       (\_ -> case-max (\w -> min x z ≤ min x w) y z
                                (\zy -> min-glb x y _ (min-left x z)
                                          ( chain>
                                            min x z === z  by  min-right x z
                                                    === y  by  zy
                                          )
                                )
                                (\_  -> refl _)
                       )

module DistributivityB {A : Set}(Ord : DecidableOrder A) where

  private
    -- We need to η-expand to get Dual (Dual Ord') = Ord'
    Ord' = η Ord
    module DistrOrd  = DistributivityA (Dual Ord')
    module MinMaxOrd = MinMax Ord'

  open MinMaxOrd

  open DistrOrd public renaming (min-max-distr to max-min-distr)

--   max-min-distr : forall x y z -> max x (min y z) ≡ min (max x y) (max x z)
--   max-min-distr = DistrOrd.min-max-distr

module Distributivity {A : Set}(Ord : DecidableOrder A) where

  private
    module DistrA = DistributivityA Ord
    module DistrB = DistributivityB Ord

  open DistrA public
  open DistrB public

-- Testing
postulate
  X    : Set
  OrdX : DecidableOrder X

module MinMaxX = MinMax OrdX
module DistrX = Distributivity OrdX

open MinMaxX
open DistrX

