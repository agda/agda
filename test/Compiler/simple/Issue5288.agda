-- Andreas, 2021-04-10, issue #5288
-- De Bruijn index problem in treeless compiler

-- {-# OPTIONS -v tc.cc:20 #-}
-- {-# OPTIONS -v treeless:40 #-}
-- {-# OPTIONS -v treeless.convert.lambdas:40 #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

f : Nat → Nat → Nat
f _ zero = 0
f m      = λ _ → m   -- this catch-all was wrongly compiled

postulate
  printNat : Nat → IO ⊤

{-# COMPILE GHC printNat = print #-}
{-# COMPILE JS  printNat = function (x) { return function(cb) { process.stdout.write(x + "\n"); cb(0); }; } #-}

test : Nat
test = f 123 1

prf : test ≡ 123
prf = refl

main = printNat test

-- Should print 123
