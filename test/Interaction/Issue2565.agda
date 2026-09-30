
open import Agda.Builtin.Nat
open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Agda.Builtin.FromString
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.Int

instance
  NumberNat : Number Nat
  Number.Constraint NumberNat _ = ⊤
  Number.fromNat NumberNat n = n

  StringIsString : IsString String
  IsString.Constraint StringIsString _ = ⊤
  IsString.fromString StringIsString s = s

  ListIsString : IsString (List Char)
  IsString.Constraint ListIsString _ = ⊤
  IsString.fromString ListIsString s = primStringToList s

  NegativeInt : Negative Int
  Negative.Constraint NegativeInt _ = ⊤
  Negative.fromNeg NegativeInt zero = pos 0
  Negative.fromNeg NegativeInt (suc n) = negsuc n

abs : Int → Nat
abs (pos n) = n
abs (negsuc n) = suc n

postulate _+Z_ : Int → Int → Int

append : ∀ {a} {A : Set a} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

-- no paren
give1 : Nat
give1 = suc {!4!}

-- paren
give2 : Nat
give2 = suc {!fromNat 4!}

-- no paren
give3 : List Char
give3 = append "foo" {!"bar"!}

-- paren
give4 : List Char
give4 = append "foo" {!fromString "bar"!}

-- no paren
give5 : Nat
give5 = abs {!-4!}

-- paren
give6 : Nat
give6 = abs {!fromNeg 4!}

-- 4 + ?
refine1 : Nat
refine1 = {!_+_ 4!}

-- fromNat 4 + ?
refine2 : Nat
refine2 = {!_+_ (fromNat 4)!}

-- append "foo" ?
refine3 : List Char
refine3 = {!append "foo"!}

-- append (fromString "foo") ?
refine4 : List Char
refine4 = {!append (fromString "foo")!}

-- -4 +Z ?
refine5 : Int
refine5 = {!-4 +Z_!}

-- fromNeg 4 +Z ?
refine6 : Int
refine6 = {!fromNeg 4 +Z_!}

postulate
  P : Nat → Int → List Char → Set

-- No fromXs in the goal
goal : P 4 -5 "6"
goal = {!!}
