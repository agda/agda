
module Common.Prelude where

{-# IMPORT Common.FFI #-}

import Common.Level

data   ⊥ : Set where
record ⊤ : Set where

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

{-# COMPILED_DATA Nat Common.FFI.Nat Common.FFI.Zero Common.FFI.Suc #-}

{-# COMPILED_JS     Nat function (x,v) { return (x < 1? v.zero(): v.suc(x-1)); } #-}
{-# COMPILED_JS     zero 0 #-}
{-# COMPILED_JS     suc function (x) { return x+1; } #-}

infixl 7 _*_
infixl 6 _+_ _∸_

_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}
{-# COMPILED_JS _+_ function (x) { return function (y) { return x+y; }; } #-}

_*_ : Nat → Nat → Nat
zero  * n = zero
suc m * n = n + m * n

{-# BUILTIN NATTIMES _*_ #-}
{-# COMPILED_JS _*_ function (x) { return function (y) { return x*y; }; } #-}

_∸_ : Nat → Nat → Nat
m     ∸ zero  = m
zero  ∸ _     = zero
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATMINUS _∸_ #-}
{-# COMPILED_JS _∸_ function (x) { return function (y) { return Math.max(0,x-y); }; } #-}

pred : Nat → Nat
pred zero    = zero
pred (suc n) = n


data List A : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 40 _∷_ _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL []    #-}
{-# BUILTIN CONS _∷_  #-}

{-# COMPILED_DATA List [] [] (:) #-}

data Bool : Set where
  true false : Bool

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

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
