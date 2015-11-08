module MultipleIdentifiersOneSignature where

data Bool : Set where
  false true : Bool

not : Bool → Bool
not true = false
not false = true

data Suit : Set where
  ♥ ♢ ♠ ♣ : Suit

record R : Set₁ where
  field
    A B C : Set

postulate
  A Char : Set
  B C    : Set

{-# BUILTIN CHAR  Char  #-}
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

primitive
  primIsDigit primIsSpace : Char → Bool

.b : Bool
b = true

f g h : Bool
f = true
g = false
h = true

.i j .k : Bool
i = not b
j = true
k = not (not b)
