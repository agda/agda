
module Agda.Builtin.Nat where

open import Agda.Builtin.Bool

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

infix  4 _==N_
infixl 6 _+N_ _-N_
infixl 7 _*N_

_+N_ : Nat → Nat → Nat
zero  +N m = m
suc n +N m = suc (n +N m)

_-N_ : Nat → Nat → Nat
n     -N zero = n
zero  -N suc m = zero
suc n -N suc m = n -N m

{-# BUILTIN NATPLUS _+N_ #-}
{-# BUILTIN NATMINUS _-N_ #-}

_*N_ : Nat → Nat → Nat
zero  *N m = zero
suc n *N m = m +N n *N m

{-# BUILTIN NATTIMES _*N_ #-}

_==N_ : Nat → Nat → Bool
zero  ==N zero  = true
suc n ==N suc m = n ==N m
_     ==N _     = false

{-# BUILTIN NATEQUALS _==N_ #-}

_<N_ : Nat → Nat → Bool
_     <N zero  = false
zero  <N suc _ = true
suc n <N suc m = n <N m

{-# BUILTIN NATLESS _<N_ #-}

div-helper : Nat → Nat → Nat → Nat → Nat
div-helper k m  zero    j      = k
div-helper k m (suc n)  zero   = div-helper (suc k) m n m
div-helper k m (suc n) (suc j) = div-helper k m n j

{-# BUILTIN NATDIVSUCAUX div-helper #-}

mod-helper : Nat → Nat → Nat → Nat → Nat
mod-helper k m  zero    j      = k
mod-helper k m (suc n)  zero   = mod-helper 0 m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

{-# BUILTIN NATMODSUCAUX mod-helper #-}
