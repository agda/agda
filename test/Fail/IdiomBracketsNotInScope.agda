
module _ where

open import Agda.Builtin.Nat

postulate
  F : Set → Set
  pure : ∀ {A} → A → F A
  -- _<*>_ : ∀ {A B} → F (A → B) → F A → F B

fail : F Nat → F Nat
fail a = (| suc a |)
