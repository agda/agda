
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
suc n *N m = n *N m +N m

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

divAux : Nat → Nat → Nat → Nat → Nat
divAux k m  zero    j      = k
divAux k m (suc n)  zero   = divAux (suc k) m n m
divAux k m (suc n) (suc j) = divAux k m n j

{-# BUILTIN NATDIVSUCAUX divAux #-}

modAux : Nat → Nat → Nat → Nat → Nat
modAux k m  zero    j      = k
modAux k m (suc n)  zero   = modAux 0 m n m
modAux k m (suc n) (suc j) = modAux (suc k) m n j

{-# BUILTIN NATMODSUCAUX modAux #-}
