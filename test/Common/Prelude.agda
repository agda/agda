
module Common.Prelude where

postulate String : Set

{-# BUILTIN STRING String #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN ZERO    zero #-}

_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)

_∸_ : Nat → Nat → Nat
m     ∸ zero  = m
zero  ∸ _     = zero
suc m ∸ suc n = m ∸ n

data List A : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 40 _∷_

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL []    #-}
{-# BUILTIN CONS _∷_  #-}

data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_DATA Bool Bool True False #-}
