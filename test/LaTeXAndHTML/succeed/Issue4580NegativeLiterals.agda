-- Andreas, 2020-04-12, issue #4580
-- Highlighting for builtins FROMNAT, FROMNEG, FROMSTRING

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record Number (A : Set) : Set where
  field fromNat : Nat → A

record Negative (A : Set) : Set where
  field fromNeg : Nat → A

open Number {{...}} public
open Negative {{...}} public

{-# BUILTIN FROMNAT fromNat #-}  -- Should be highlighted.
{-# BUILTIN FROMNEG fromNeg #-}  -- Jump to definition should work.

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

thm : -5 ≡ neg 4
thm = refl
