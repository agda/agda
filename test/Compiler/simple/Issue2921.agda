
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

data Unit : Set where
  c : ⊤ → Nat → ⊤ → Unit

-- Note that the ⊤ arguments do not get erased and should be present in
-- the Haskell version of Unit.
{-# FOREIGN GHC data Unit = Unit () Integer () #-}
{-# COMPILE GHC Unit = data Unit (Unit) #-}

postulate print : Nat → IO ⊤
{-# COMPILE GHC print = print #-}
{-# COMPILE JS  print = function (x) { return function(cb) { process.stdout.write(x + "\n"); cb(0) } } #-}

foo : Unit → IO ⊤
foo (c _ n _) = print n

main : IO ⊤
main = foo (c _ 12345 _)
