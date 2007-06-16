------------------------------------------------------------------------
-- Some examples showing the solver in action
------------------------------------------------------------------------

module Prelude.SemiringSolver.Examples where

open import Prelude.Algebraoid.Conversion
open import Prelude.Logic
open import Prelude.Nat
open import Prelude.Nat.Properties
open import Prelude.Bool
open import Prelude.Bool.Properties
open import Prelude.Fin
open import Prelude.Vec
import Prelude.Algebra.Operations
private
  open module ON =
    Prelude.Algebra.Operations
      (commSemiringoid⟶semiringoid ℕ-commSemiringoid)
    using (_^_)
  open module OB =
    Prelude.Algebra.Operations
      (commSemiringoid⟶semiringoid
         (commRingoid⟶commSemiringoid Bool-commRingoid-xor-∧))
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
    open Bool-xor-semiringSolver
    X = var fz
    Y = var (fs fz)
