-- The part up to "data D" could be replaced by "open import
-- Common.Prelude", but at the time of writing that seems to slow down
-- the test by something like a factor of two or three (for the GHC
-- backend, on one system).

{-# OPTIONS --erasure #-}

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

postulate
  putStr : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStr = Data.Text.IO.putStr #-}
{-# COMPILE JS putStr =
    function (x) {
      return function(cb) {
        process.stdout.write(x); cb(0); }; } #-}

data D : Set where
  @0 c : D

f : @0 D → String
f c = "Success\n"

main : IO ⊤
main = putStr (f c)
