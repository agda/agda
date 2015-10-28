module Common.Integer where

open import Common.Nat

data Integer : Set where
  pos : Nat → Integer
  negsuc : Nat → Integer

{-# BUILTIN INTEGER Integer #-}
{-# BUILTIN INTEGERPOS pos #-}
{-# BUILTIN INTEGERNEGSUC negsuc #-}
