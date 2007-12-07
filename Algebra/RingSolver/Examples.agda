------------------------------------------------------------------------
-- Some examples showing the solver in action
------------------------------------------------------------------------

module Algebra.RingSolver.Examples where

open import Logic
open import Data.Function
open import Data.Vec
open import Data.Fin
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool
open import Data.Bool.Properties
import Algebra.Operations as Op
import Algebra.RingSolver as S
import Algebra.Props.CommutativeSemiring as CSProp
import Algebra.Props.CommutativeRing     as CRProp
import Algebra.Props.AlmostCommRing      as ACRProp
open Op (CSProp.semiringoid ℕ-commSemiringoid) using (_^_)
open Op (CRProp.semiringoid Bool-commRingoid-xor-∧)
  renaming (_^_ to _↑_)

abstract

  example₁
    :  forall x y
    -> (x + y) ^ 3 ≡ x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3
  example₁ x y =
    prove (x ∷ y ∷ [])
          ((X :+ Y) :^ 3)
          (X :^ 3 :+ con 3 :* X :^ 2 :* Y :+
           con 3 :* X :* Y :^ 2 :+ Y :^ 3)
          ≡-refl
    where
    open ℕ-semiringSolver
    X = var fz
    Y = var (fs fz)

  example₂
    :  forall x y
    -> (x xor y) ↑ 3 ≡ x ↑ 3 xor x ↑ 2 ∧ y xor x ∧ y ↑ 2 xor y ↑ 3
  example₂ x y =
    prove (x ∷ y ∷ [])
          ((X :+ Y) :^ 3)
          (X :^ 3 :+ (X :^ 2 :* Y :+ (X :* Y :^ 2 :+ Y :^ 3)))
          ≡-refl
    where
    open Bool-xor-ringSolver
    X = var fz
    Y = var (fs fz)

  example₃ : forall x -> x xor x ≡ false
  example₃ x = prove (x ∷ []) (X :+ X) (con false) ≡-refl
    where
    open Bool-xor-ringSolver
    X = var fz
