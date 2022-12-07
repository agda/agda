{-# OPTIONS --cubical --erasure --save-metas #-}

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

open import Erased-cubical-Pattern-matching-Cubical
open import Erased-cubical-Pattern-matching-Erased

postulate
  putStr : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStr = Data.Text.IO.putStr #-}
{-# COMPILE JS putStr =
    function (x) {
      return function(cb) {
        process.stdout.write(x); cb(0); }; } #-}

main : IO ⊤
main = putStr (f c₁)
