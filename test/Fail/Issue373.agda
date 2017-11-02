module Issue373 where

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

{-# FOREIGN GHC data Nat = Zero | Suc Nat #-}
{-# COMPILE GHC Nat = data Nat (Zero | Suc) #-} -- should fail when compiling
