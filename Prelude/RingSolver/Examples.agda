------------------------------------------------------------------------
-- Some examples showing the solver in action
------------------------------------------------------------------------

module Prelude.SemiringSolver.Examples where

open import Prelude.Logic
open import Prelude.Function
open import Prelude.Nat
open import Prelude.Nat.Properties
open import Prelude.Bool
open import Prelude.Bool.Properties
import Prelude.Int as Int
open import Prelude.Fin
open import Prelude.Vec
import Prelude.Algebra.Operations as Op
import Prelude.RingSolver as S
import Prelude.RingSolver.Int as IS
import Prelude.Algebra.CommutativeSemiringProperties as CSProp
import Prelude.Algebra.CommutativeRingProperties     as CRProp
import Prelude.Algebra.AlmostCommRingProperties      as ACRProp
private
  open module ON =
    Op (CSProp.semiringoid ℕ-commSemiringoid) using (_^_)
  open module OB =
    Op (CRProp.semiringoid Bool-commRingoid-xor-∧)
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

  example₃
    :  forall x y
    -> Int.-_ (Int._*_ x y) ≡ Int._*_ (Int.-_ x) y
  example₃ x y =
    prove (x ∷ y ∷ []) (:- (X :* Y)) (:- X :* Y) ≡-refl
    where
    open Int.ℤ-ringSolver
    X = var fz
    Y = var (fs fz)

  example₄
    :  forall x y
    -> (x ∨ y) ↑ 3 ≡ x ↑ 3 ∨ 3 × x ↑ 2 ∧ y ∨ 3 × x ∧ y ↑ 2 ∨ y ↑ 3
  example₄ x y =
    prove (x ∷ y ∷ [])
          ((X :+ Y) :^ 3)
          (X :^ 3 :+ (con 3 :* X :^ 2 :* Y :+ (con 3 :* X :* Y :^ 2 :+ Y :^ 3)))
          ≡-refl
    where
    open module IS' =
           IS (CSProp.almostCommRingoid Bool-commSemiringoid-∨-∧)
    X = var fz
    Y = var (fs fz)

  example₅ : forall x -> x xor x ≡ false
  example₅ x = prove (x ∷ []) (X :+ X) (con false) ≡-refl
    where
    open Bool-xor-ringSolver
    X = var fz
