{-# OPTIONS --guardedness #-}

module CoinductiveBuiltinList where

open import Common.Coinduction

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : ∞ (List A)) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}
