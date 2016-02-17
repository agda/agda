module Common.Nat where

open import Agda.Builtin.Nat public
  using    ( Nat; zero; suc; _+_; _*_ )
  renaming ( _-_ to _∸_ )

{-# COMPILED_JS Nat function (x,v) { return (x < 1? v.zero(): v.suc(x-1)); } #-}
{-# COMPILED_JS zero 0 #-}
{-# COMPILED_JS suc function (x) { return x+1; } #-}

{-# COMPILED_JS _+_ function (x) { return function (y) { return x+y; }; } #-}
{-# COMPILED_JS _*_ function (x) { return function (y) { return x*y; }; } #-}
{-# COMPILED_JS _∸_ function (x) { return function (y) { return Math.max(0,x-y); }; } #-}

pred : Nat → Nat
pred zero    = zero
pred (suc n) = n

