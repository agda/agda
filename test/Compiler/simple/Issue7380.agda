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
{-# COMPILE JS  print = x => cb => { process.stdout.write(x.toString() + "\n"); cb(0); } #-}

main = print (f (record { x = 3 }))
