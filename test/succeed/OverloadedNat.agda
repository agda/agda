
open import Common.Prelude

record IsNumber (A : Set) : Set where
  field fromNat : Nat → A

open IsNumber {{...}} public

{-# BUILTIN FROMNAT fromNat #-}

instance
  IsNumberNat : IsNumber Nat
  IsNumberNat = record { fromNat = λ n → n }

data Int : Set where
  pos : Nat → Int
  neg : Nat → Int

instance
  IsNumberInt : IsNumber Int
  IsNumberInt = record { fromNat = pos }

fiveN : Nat
fiveN = 5

fiveZ : Int
fiveZ = 5

open import Common.Equality

thm : pos 5 ≡ 5
thm = refl
