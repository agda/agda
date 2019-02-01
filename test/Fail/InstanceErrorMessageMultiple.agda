
module _ where

record Semiring (A : Set) : Set where
  infixl 6 _+_
  field _+_ : A → A → A

open Semiring {{...}} public

infix 4 _≡_

postulate
  Ord : Set → Set
  Nat Bool  : Set
  zero  : Nat
  _≡_   : Nat → Nat → Set
  refl  : ∀ {x} → x ≡ x
  to    : ∀ {x} y → x ≡ y
  trans : {x y z : Nat} → x ≡ y → y ≡ z → x ≡ z

  instance
    ringNat′ : Semiring Nat

  _+N_ : Nat → Nat → Nat

instance
  ringNat : Semiring Nat
  ringNat ._+_ = _+N_

bad : (a b c : Nat) → a +N b ≡ c +N a
bad a b c =
  trans (to (a + c)) refl

-- Should list the errors from testing both ringNat and ringNat′
