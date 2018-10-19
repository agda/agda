
module _ where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

variable
  ℓ : Level
  A B C : Set ℓ

infixr 1 _×_ _,_
record _×_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : A
    snd : B

module _ (x : A) (y : B) where
  f : C → A × B × C
  f z = x , y , z

check : (x : B) (y : C) (z : A) → f x y z ≡ (x , y , z)
check x y z = refl
