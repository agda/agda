
module Common.Prelude where

postulate Char : Set

{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}

postulate String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN ZERO    zero #-}

{-# COMPILED_DATA Nat Common.FFI.Nat Common.FFI.Zero Common.FFI.Suc #-}

{-# COMPILED_JS     Nat function (x,v) { return (x < 1? v.zero(): v.suc(x-1)); } #-}
{-# COMPILED_JS     zero 0 #-}
{-# COMPILED_JS     suc function (x) { return x+1; } #-}

_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)

{-# COMPILED_JS _+_ function (x) { return function (y) { return x+y; }; } #-}

_∸_ : Nat → Nat → Nat
m     ∸ zero  = m
zero  ∸ _     = zero
suc m ∸ suc n = m ∸ n

{-# COMPILED_JS _∸_ function (x) { return function (y) { return Math.max(0,x-y); }; } #-}

data List A : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 40 _∷_

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL []    #-}
{-# BUILTIN CONS _∷_  #-}

{-# COMPILED_DATA List [] [] (:) #-}

data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_DATA Bool Bool True False #-}

{-# COMPILED_JS Bool function (x,v) { return (x? v["true"](): v["false"]()); } #-}
{-# COMPILED_JS true true #-}
{-# COMPILED_JS false false #-}

data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}

postulate
  IO : Set → Set

{-# COMPILED_TYPE IO IO #-}
{-# BUILTIN IO IO #-}
