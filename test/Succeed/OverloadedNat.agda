
open import Common.Prelude

record IsNumber (A : Set) : Set where
  field fromNat : Nat → A

open IsNumber {{...}} public

{-# BUILTIN FROMNAT fromNat #-}

instance
  IsNumberNat : IsNumber Nat
  IsNumberNat = record { fromNat = λ n → n }

record IsNegative (A : Set) : Set where
  field fromNeg : Nat → A

open IsNegative {{...}} public

{-# BUILTIN FROMNEG fromNeg #-}

data Int : Set where
  pos : Nat → Int
  neg : Nat → Int

instance
  IsNumberInt : IsNumber Int
  IsNumberInt = record { fromNat = pos }

  IsNegativeInt : IsNegative Int
  IsNegativeInt = record { fromNeg = neg }

fiveN : Nat
fiveN = 5

fiveZ : Int
fiveZ = 5

minusFive : Int
minusFive = -5

open import Common.Equality

thm : pos 5 ≡ 5
thm = refl

thm′ : neg 5 ≡ -5
thm′ = refl
