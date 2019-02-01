
module _ where

record Semiring (A : Set) : Set where
  infixl 6 _+_
  field _+_ : A → A → A

open Semiring {{...}} public

infix 4 _≡_

postulate
  Nat Bool  : Set
  _≡_   : Nat → Nat → Set
  refl  : ∀ {x} → x ≡ x
  to    : ∀ {x} (y : Nat) → x ≡ y
  trans : {x y z : Nat} → x ≡ y → y ≡ z → x ≡ z

  instance _ : Semiring Nat
           _ : Semiring Bool

bad : (a b c : Nat) → a + b ≡ c + a
bad a b c =
  trans (to (a + c)) refl

-- Should complain about a != c when checking refl, not a missing instance Semiring Nat.
