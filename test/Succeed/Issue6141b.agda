
module _ where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.FromNat

instance
  fromNatNat : Number Nat
  fromNatNat .Number.Constraint _ = ⊤
  fromNatNat .fromNat n = n

private
 variable
   ℓ : Level
   A : Set ℓ

postulate
  Vec : (A : Set ℓ) (n : Nat) → Set ℓ
  foo : {n : Nat} (xs : Vec A n) (ys : Vec A 0) → Nat
