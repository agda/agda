module Issue373 where

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

{-# FOREIGN GHC data Nat = Zero | Suc Nat #-}
{-# COMPILE GHC Nat = data Nat (Zero | Suc) #-} -- should fail when compiling

-- Conflicting GHC pragmas for Nat at
--   - test/Fail/Issue373.agda:7.1-28
--   - test/Fail/Issue373.agda:10.1-48
