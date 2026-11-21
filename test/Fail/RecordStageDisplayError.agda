module RecordStageDisplayError where

open import Agda.Builtin.Bool

record RF : Set₁ where
  field A : Set
  F : Bool → Set
  F true  = A
  F false = A → A
  field value : (b : Bool) → F b

-- The error should mention RF.1.F, not the nested implementation modules.
bad : RF
bad = record { A = Bool ; value = λ b → true }
