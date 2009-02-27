module CoinductiveBuiltinNatural2 where

codata ∞ (A : Set) : Set where
  ♯_ : A → ∞ A

data ℕ : Set where
  zero : ℕ
  suc  : (n : ∞ ℕ) → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
