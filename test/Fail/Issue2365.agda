open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.Equality

fromNeg : Nat → Int
fromNeg zero    = pos 0
fromNeg (suc x) = negsuc x

{-# BUILTIN FROMNEG fromNeg #-}

-- A negative number

neg : Int
neg = -20

-- Matching against negative numbers

lit : Int → Nat
lit -20 = 0  -- Error thrown here
lit _   = 1

-- Testing reduction rules

test0 : lit -20 ≡ 0
test0 = refl

test1 : lit -2 ≡ 1
test1 = refl

-- Error WAS:  Internal error in expandLitPattern
-- Error THEN: Type mismatch when checking that the pattern -20 has type Int
-- Error NOW:  Negative literals are not supported in patterns

-- Ideally, this would succeed.
