------------------------------------------------------------------------
-- The Agda standard library
--
-- An example of how Algebra.CommutativeMonoidSolver can be used
------------------------------------------------------------------------

module Algebra.CommutativeMonoidSolver.Example where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; isEquivalence)

open import Data.Bool.Base using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Bool.Properties

open import Data.Fin using (zero; suc)
open import Data.Vec using ([]; _∷_)

open import Algebra using (CommutativeMonoid)

∨-cm : CommutativeMonoid _ _
∨-cm = record
  { Carrier = Bool
  ; _≈_     = _≡_
  ; _∙_     = _∨_
  ; ε       = false
  ; isCommutativeMonoid = record
    { isSemigroup = ∨-isSemigroup
    ; identityˡ = ∨-identityˡ
    ; comm      = ∨-comm
    }
  }

open import Algebra.CommutativeMonoidSolver ∨-cm

test : ∀ x y z → (x ∨ y) ∨ (x ∨ z) ≡ (z ∨ y) ∨ (x ∨ x)
test a b c = let _∨_ = _⊕_ in
  prove 3 ((x ∨ y) ∨ (x ∨ z)) ((z ∨ y) ∨ (x ∨ x)) (a ∷ b ∷ c ∷ [])
  where
  x = var zero
  y = var (suc zero)
  z = var (suc (suc zero))
