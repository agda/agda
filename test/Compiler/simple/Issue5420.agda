open import Agda.Builtin.IO
open import Agda.Builtin.Reflection
open import Agda.Builtin.String
open import Agda.Builtin.Unit

_>>=_ : {A B : Set} → TC A → (A → TC B) → TC B
_>>=_ = λ x f → bindTC x f

postulate
  putStr : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStr = Data.Text.IO.putStr #-}
{-# COMPILE JS putStr =
    function (x) {
      return function(cb) {
        process.stdout.write(x); cb(0); }; } #-}

main : IO ⊤
main = putStr "Success\n"
