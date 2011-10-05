module Prelude.Nat where

open import Prelude.Bool

{-# IMPORT PrimNat #-}

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO Z #-}
{-# BUILTIN SUC S #-}
{-# COMPILED_DATA Nat PrimNat.N PrimNat.Z PrimNat.S #-}

infixl 30 _+_

_+_ : Nat -> Nat -> Nat
Z + m = m
S n + m = S (n + m)

_*_ : Nat -> Nat -> Nat
Z * m = Z
S n * m = (n * m) + m

_-_ : Nat -> Nat -> Nat
n     - Z     = n
(S n) - (S m) = n - m
Z     - _     = Z

_<_ : Nat -> Nat -> Bool
_ < Z   = false
Z   < S _ = true
S n < S m = n < m

Nid : Nat -> Bool -> Bool
Nid Z true = true
Nid Z false = false
Nid (S n) m =  (Nid n ( m))

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _-_ #-}
-- {-# BUILTIN NATLESS _<_ #-}
-- {-# BUILTIN NATEQUALS __ #-}
