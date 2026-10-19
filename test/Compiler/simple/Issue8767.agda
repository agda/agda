open import Agda.Builtin.Nat
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

postulate
  print : Nat → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC print = \n -> print (n :: Integer) #-}
{-# COMPILE JS print = n => k => k(console.log("" + n)) #-}

add : Nat → Nat → Nat
add zero    n = n
add (suc m) n = add m (suc n)

-- This code should not be executed. If it is, then the test case
-- might effectively hang.

slow : Nat → Nat
slow = add 1_000000000_000000000_000000000

zero-if-zero : Nat → Nat → Nat
zero-if-zero zero    _ = 0
zero-if-zero (suc _) n = n

{-# INLINE zero-if-zero #-}

f : Nat → Nat
f zero    = 0
f (suc n) = zero-if-zero n (slow n)

main : IO ⊤
main = print (f 0)
