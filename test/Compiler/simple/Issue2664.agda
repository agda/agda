-- Andreas, 2017-08-10, issue #2664, reported by csetzer
-- Test case by Ulf

-- {-# OPTIONS -v tc.rec:40 #-}
-- {-# OPTIONS -v tc.cc:60 #-}

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

mutual
  -- Error WAS:
  -- The presence of mutual affected the compilation of the projections
  -- since it triggered a record pattern translation for them.

  record R : Set where
    constructor mkR
    field
      dummy : Nat
      str : String

helloWorld : R
helloWorld = mkR 0 "Hello World!"

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE JS  putStrLn = function(x) { return function(cb) { process.stdout.write(x + "\n"); cb(0); }; } #-}

main : IO ⊤
main = putStrLn (R.str helloWorld)

-- Expected: Should print
--
--   Hello World!
