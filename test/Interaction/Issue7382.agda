-- Andreas, 2024-07-22, issue #7382
-- Test case by Andre Knispel, fixed by Andras Kovacs

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

record R : Set where
  field x : Nat

variable r : R

data D : R → Nat → Set where
  c : let open R r in D r x

f : R → Nat
f r = fst g
  where
    g : Σ Nat (D r)
    g = (_ , c)

postulate print : Nat → IO ⊤
{-# COMPILE GHC print = print #-}

main = print (f (record { x = 3 }))

-- This used to crash when compiled twice (due to deadcode serialization bug).
