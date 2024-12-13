{-# OPTIONS --cubical #-}
module EtaHComp where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Cubical.Glue; open Helpers public
open import Agda.Primitive.Cubical
  renaming (primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primComp to comp ; primHComp to hcomp ; primTransp to transp)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat

data S¹ : Type where
  base : S¹
  loop : base ≡ base

_×_ : (A : Type) (B : Type) → Type
A × B = Σ A (λ _ → B)
infixr 5 _×_

T = PathP (λ i → S¹ × S¹) (base , base) (base , base)

t1 : T
t1 = λ j → transp (λ _ → S¹ × S¹) i0
             (hcomp (λ i → λ { (j = i0) → (base , base)
                             ; (j = i1) → (base , base)
                             })
                    (base , base))

t4 : T
t4 = (λ j → hcomp {A = S¹ × S¹}
                  (λ i → λ { (j = i0) → (base , base)
                           ; (j = i1) → (base , base)
                           })
                  (base , base))

-- Eta-expansion was not kicking in for hcomp/transp for record values,
-- since they look like neutrals (both are headed by a Def, and neither
-- primHComp/primTransp have copatterns in their definition).

test : PathP (λ i → T) t1 t4
test = refl
