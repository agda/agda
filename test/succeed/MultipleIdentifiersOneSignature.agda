module MultipleIdentifiersOneSignature where

data Bool : Set where
  false true : Bool

codata Suit : Set where
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
