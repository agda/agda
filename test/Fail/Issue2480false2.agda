-- Exploit by Jesper Cockx

open import Agda.Builtin.Equality

data Bool : Set where
  tt ff : Bool

const : Bool → (Bool → Bool)
const = λ x _ → x

mutual
  Bool→cBool : Set
  Bool→cBool = _

  const-tt : Bool→cBool
  const-tt = const tt

constant : (f : Bool→cBool) (x y : Bool) → f x ≡ f y
constant f x y = refl

constant' : (f : Bool → Bool) (x y : Bool) → f x ≡ f y
constant' = constant

swap : Bool → Bool
swap tt = ff
swap ff = tt

fireworks : tt ≡ ff
fireworks = constant' swap ff tt
