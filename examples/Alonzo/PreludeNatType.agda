module PreludeNatType where

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}
  {-# BUILTIN SUC suc #-}
  {-# BUILTIN ZERO zero #-}
