{-# OPTIONS -vtc.record.where:30 #-}
module Issue7805b where

open import Agda.Builtin.Nat

auto : {X : Set} ⦃ _ : X ⦄ → X
auto ⦃ x ⦄ = x

record X : Set₁ where
  field it : ⦃ A : Nat ⦄ → Nat

_ = record where it = auto + 1
