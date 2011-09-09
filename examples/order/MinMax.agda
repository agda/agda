module MinMax where

open import Prelude
open import Logic.Base
open import Logic.Relations
open import Logic.Identity using (_≡_)
import Logic.ChainReasoning
open import DecidableOrder as DecOrder

module Min {A : Set}(Ord : DecidableOrder A) where

  open DecidableOrder Ord

  min : A → A → A
  min a b with decide a b
  ... | \/-IL _ = a
  ... | \/-IR _ = b

  data CaseMin x y : A → Set where
    leq : x ≤ y → CaseMin x y x
    geq : x ≥ y → CaseMin x y y

  case-min′ : ∀ x y → CaseMin x y (min x y)
  case-min′ x y with decide x y
  ... | \/-IL xy  = leq xy
  ... | \/-IR ¬xy with total x y
  ...   | \/-IL xy = elim-False (¬xy xy)
  ...   | \/-IR yx = geq yx

  case-min : (P : A → Set)(x y : A) →
            (x ≤ y → P x) →
            (y ≤ x → P y) → P (min x y)
  case-min P x y ifx ify with min x y | case-min′ x y
  ... | .x | leq xy = ifx xy
  ... | .y | geq yx = ify yx

  min-glb : ∀ x y z → z ≤ x → z ≤ y → z ≤ min x y
  min-glb x y z zx zy with min x y | case-min′ x y
  ... | .x | leq _ = zx
  ... | .y | geq _ = zy

  min-left : ∀ x y → min x y ≤ x
  min-left x y with min x y | case-min′ x y
  ... | .x | leq _  = refl _
  ... | .y | geq yx = yx

  min-right : ∀ x y → min x y ≤ y
  min-right x y with min x y | case-min′ x y
  ... | .x | leq xy = xy
  ... | .y | geq _  = refl _

  min-sym : ∀ x y → min x y ≡ min y x
  min-sym x y = antisym _ _ (lem x y) (lem y x)
    where
      lem : ∀ a b → min a b ≤ min b a
      lem a b with min b a | case-min′ b a
      ... | .b | leq _ = min-right _ _
      ... | .a | geq _ = min-left _ _

Dual : {A : Set} → DecidableOrder A → DecidableOrder A
Dual Ord = record
    { _≤_     = _≥_
    ; refl    = refl
    ; antisym = \x y xy yx   → antisym _ _ yx xy
    ; trans   = \x y z xy yz → trans _ _ _ yz xy
    ; total   = \x y         → total _ _
    ; decide  = \x y         → decide _ _
    }
  where
    open DecidableOrder Ord

module Max {A : Set}(Ord : DecidableOrder A)
      = Min (Dual Ord) renaming
              ( min       to max
              ; case-min  to case-max
              ; case-min′ to case-max′
              ; CaseMin   to CaseMax
              ; module CaseMin to CaseMax
              ; leq       to geq
              ; geq       to leq
              ; min-glb   to max-lub
              ; min-sym   to max-sym
              ; min-right to max-right
              ; min-left  to max-left
              )

module MinMax {A : Set}(Ord : DecidableOrder A) where
  open DecidableOrder Ord public
  open Min Ord public
  open Max Ord public

module DistributivityA {A : Set}(Ord : DecidableOrder A) where

  open MinMax Ord

  min-max-distr : ∀ x y z → min x (max y z) ≡ max (min x y) (min x z)
  min-max-distr x y z = antisym _ _ left right
    where
      open Logic.ChainReasoning.Mono.Homogenous _≤_ refl trans

      left : min x (max y z) ≤ max (min x y) (min x z)
      left with max y z | case-max′ y z
      ... | .z | Min.geq _ = max-right _ _
      ... | .y | Min.leq _ = max-left _ _

      right : max (min x y) (min x z) ≤ min x (max y z)
--      right with max (min x y) (min x z) | case-max′ (min x y) (min x z)
      right = case-max (\w → w ≤ min x (max y z)) (min x y) (min x z)
                       (\_ → case-max (\w → min x y ≤ min x w) y z
                                (\_  → refl _)
                                (\yz → min-glb x z _ (min-left x y)
                                          ( chain>
                                            min x y === y  by  min-right x y
                                                    === z  by  yz
                                          )
                                )
                       )
                       (\_ → case-max (\w → min x z ≤ min x w) y z
                                (\zy → min-glb x y _ (min-left x z)
                                          ( chain>
                                            min x z === z  by  min-right x z
                                                    === y  by  zy
                                          )
                                )
                                (\_  → refl _)
                       )

module DistributivityB {A : Set}(Ord : DecidableOrder A) where

  open DistributivityA (Dual Ord) public renaming (min-max-distr to max-min-distr)

module Distributivity {A : Set}(Ord : DecidableOrder A) where

  open DistributivityA Ord public
  open DistributivityB Ord public

-- Testing
postulate
  X    : Set
  OrdX : DecidableOrder X

-- open DecidableOrder OrdX
open MinMax OrdX -- hiding (_≤_)
open Distributivity OrdX

open Logic.ChainReasoning.Mono.Homogenous

-- Displayforms doesn't work for MinMax._≤_ (reduces to DecidableOrder._≤_)
test : ∀ x y → min x y ≤ x
test x y = min-left x y
