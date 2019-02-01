{-# OPTIONS --without-K #-}
module Common.Nat where

open import Agda.Builtin.Nat public
  using    ( Nat; zero; suc; _+_; _*_ )
  renaming ( _-_ to _∸_ )


pred : Nat → Nat
pred zero    = zero
pred (suc n) = n

