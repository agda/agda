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
open import Prelude.Fin
open import Prelude.Vec
import Prelude.Algebra.Operations as Op
import Prelude.Algebra.CommutativeSemiringProperties as CSProp
import Prelude.Algebra.CommutativeRingProperties     as CRProp
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

  -- I need some ring with an interesting definition of negation...

  example₃
    :  forall x y
    -> id (x xor y) ≡ id x xor y
  example₃ x y =
    prove (x ∷ y ∷ [])
          (:- (X :+ Y))
          (:- X :+ Y)
          ≡-refl
    where
    open Bool-xor-ringSolver
    X = var fz
    Y = var (fs fz)

  -- The following example requires the coefficients to be in a
  -- different ring (or something).

  -- example₄
  --   :  forall x y
  --   -> (x ∨ y) ↑ 3 ≡ x ↑ 3 ∨ 3 × x ↑ 2 ∧ y ∨ 3 × x ∧ y ↑ 2 ∨ y ↑ 3
  -- example₄ x y =
  --   prove (x ∷ y ∷ [])
  --         ((X :+ Y) :^ 3)
  --         (X :^ 3 :+ (con 3 :* X :^ 2 :* Y :+ (con 3 :* X :* Y :^ 2 :+ Y :^ 3)))
  --         ≡-refl
  --   where
  --   open Bool-semiringSolver
  --   X = var fz
  --   Y = var (fs fz)

  example₅ : forall x -> x xor x ≡ false
  example₅ x = prove (x ∷ []) (X :+ X) (con false) ≡-refl
    where
    open Bool-xor-ringSolver
    X = var fz
