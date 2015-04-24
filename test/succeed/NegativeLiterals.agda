
open import Common.Prelude

record Number (A : Set) : Set where
  field fromNat : Nat → A

record Negative (A : Set) : Set where
  field fromNeg : Nat → A

open Number {{...}} public
open Negative {{...}} public

{-# BUILTIN FROMNAT fromNat #-}
{-# BUILTIN FROMNEG fromNeg #-}

instance
  NumberNat : Number Nat
  NumberNat = record { fromNat = λ n → n }

data Int : Set where
  pos : Nat → Int
  neg : Nat → Int

instance
  NumberInt : Number Int
  NumberInt = record { fromNat = pos }

  NegativeInt : Negative Int
  NegativeInt = record { fromNeg = λ { zero → pos 0 ; (suc n) → neg n } }

minusFive : Int
minusFive = -5

open import Common.Equality

thm : -5 ≡ neg 4
thm = refl
