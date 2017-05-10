{-# OPTIONS -v treeless:20 #-}
module _ where

data N : Set where
  zero : N
  suc : N → N

_+_ : N → N → N
zero + n = n
suc m + n = suc (m + n)

record P A B : Set where
  constructor _,_
  field fst : A
        snd : B

open P

{-# INLINE fst #-}
{-# INLINE snd #-}

-- Without handling repeated cases:
-- g = λ a → case a of b , c → b (case a of d , e → e)
-- Should be
-- g = λ a → case a of b , c → b c
g : P (N → N) N → N
g z = fst z (snd z)
