
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

_^_ : Nat → Nat → Nat
x ^ zero = 1
x ^ suc y = x * (x ^ y)

data Enum : Set where
  makeEnum : (size : Nat) → (variants : Nat) →
             .{{ _ : (variants < size) ≡ true }} → Enum

five : Enum
five = makeEnum (2 ^ 32) 5

data Expr : (t : Enum) → Set where
  constant : (x : Nat) → Expr five

func : ∀ {t} → Expr t → Bool
func (constant x) = false
