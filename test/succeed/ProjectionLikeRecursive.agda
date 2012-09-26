-- Andreas, 2012-09-26 disable projection-likeness for recursive functions
-- {-# OPTIONS -v tc.proj.like:100 #-}
module ProjectionLikeRecursive where

open import Common.Prelude
open import Common.Equality

if_then_else_ : {A : Set} → Bool → A → A → A
if true then t else e = t
if false then t else e = e

infixr 5 _∷_ _∷′_

data Vec (n : Nat) : Set where
  []  : {p : n ≡ 0} → Vec n
  _∷_ : {m : Nat}{p : n ≡ suc m} → Nat → Vec m → Vec n

null : {n : Nat} → Vec n → Bool
null [] = true
null xs = false

-- last is considered projection-like
last : (n : Nat) → Vec n → Nat
-- last 0 xs = zero  --restoring this line removes proj.-likeness and passes the file
last n [] = zero
last n (x ∷ xs) = if (null xs) then x else last _ xs
-- breaks if projection-like translation is not removing the _ in the rec. call

[]′ : Vec zero
[]′ = [] {p = refl}

_∷′_ : {n : Nat} → Nat → Vec n → Vec (suc n)
x ∷′ xs = _∷_ {p = refl} x xs

three = last 3 (1 ∷′ 2 ∷′ 3 ∷′ []′)

test : three ≡ 3
test = refl
-- Error: Incomplete pattern matching
-- when checking that the expression refl has type three ≡ 3
