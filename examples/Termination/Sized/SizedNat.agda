{-# OPTIONS  --sized-types --show-implicit #-} 

module SizedNat where

open import Size

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {↑ size}
  suc  : {size : Size} -> Nat {size} -> Nat {↑ size}

-- subtraction is non size increasing
sub : {size : Size} -> Nat {size} -> Nat {∞} -> Nat {size}
sub zero n = zero
sub (suc m) zero = suc m
sub (suc m) (suc n) = sub m n

-- div' m n  computes  ceiling(m/(n+1))
div' : {size : Size} -> Nat {size} -> Nat -> Nat {size}
div' zero    n = zero
div' (suc m) n = suc (div' (sub m n) n)

-- one can use sized types as if they were not sized
-- sizes default to ∞

add : Nat -> Nat -> Nat
add (zero ) n = n
add (suc m) n = suc (add m n)

nisse : {i : Size} -> Nat {i} -> Nat {i}
nisse zero = zero
nisse (suc zero) = suc zero
nisse (suc (suc n)) = suc zero

{- Agda complains about duplicate binding

NatInfty = Nat {∞}

{-# BUILTIN NATURAL  NatInfty  #-}
{-# BUILTIN SUC      suc       #-}
{-# BUILTIN ZERO     zero      #-}
{-# BUILTIN PLUS     add       #-}

-}

