
module Lib.Nat where

open import Lib.Bool
open import Lib.Logic
open import Lib.Id

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

infixr 50 _*_
infixr 40 _+_

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

lem-plus-zero : (n : Nat) -> n + 0 ≡ n
lem-plus-zero  zero   = refl
lem-plus-zero (suc n) = cong suc (lem-plus-zero n)

lem-plus-suc : (n m : Nat) -> n + suc m ≡ suc (n + m)
lem-plus-suc  zero   m = refl
lem-plus-suc (suc n) m = cong suc (lem-plus-suc n m)

lem-plus-commute : (n m : Nat) -> n + m ≡ m + n
lem-plus-commute n  zero   = lem-plus-zero _
lem-plus-commute n (suc m) with n + suc m | lem-plus-suc n m
... | .(suc (n + m)) | refl = cong suc (lem-plus-commute n m)

_*_ : Nat -> Nat -> Nat
zero  * m = zero
suc n * m = m + n * m

{-# BUILTIN NATPLUS  _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

_==_ : Nat -> Nat -> Bool
zero  == zero  = true
zero  == suc _ = false
suc _ == zero  = false
suc n == suc m = n == m

{-# BUILTIN NATEQUALS _==_ #-}

NonZero : Nat -> Set
NonZero zero    = False
NonZero (suc _) = True
