
module _ where

open import Agda.Builtin.Nat

postulate
  F : Set → Set
  pure : ∀ {A} → A → F A
  _<*>_ : ∀ {A B} → F (A → B) → F A → F B

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

ok : ∀ n → F Nat → F (Vec Nat n) → F (Vec Nat (suc n))
ok n a as = (| a ∷ as |)

ok₂ : ∀ n → F Nat → F (Vec Nat n) → F (Vec Nat (suc n))
ok₂ n a as = (| (_∷_ {n = n}) a as |)

fail : ∀ n → F Nat → F (Vec Nat n) → F (Vec Nat (suc n))
fail n a as = (| _∷_ {n = n} a as |)
