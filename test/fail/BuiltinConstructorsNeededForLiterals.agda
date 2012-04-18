
module BuiltinConstructorsNeededForLiterals where

data Nat : Set where
  zero : Nat → Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

data ⊥ : Set where
 
empty : Nat → ⊥
empty (zero n) = empty n
empty (suc n) = empty n

bad : ⊥
bad = empty 0
