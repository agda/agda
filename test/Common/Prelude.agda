
module Common.Prelude where

postulate String : Set

{-# BUILTIN STRING String #-}

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN ZERO    zero #-}

{-# COMPILED_JS     Nat function (x,v) { if (x < 1) { return v.zero(); } else { return v.suc(x-1); } } #-}
{-# COMPILED_JS     zero 0 #-}
{-# COMPILED_JS     suc function (x) { return (x+1); } #-}

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

data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

{-# COMPILED_DATA Bool Bool True False #-}

{-# COMPILED_JS Bool function (x,v) { if (x) { return v["true"](); } else { return v["false"](); } } #-}
{-# COMPILED_JS true true #-}
{-# COMPILED_JS false false #-}
