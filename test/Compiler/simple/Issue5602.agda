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

F : Set → Set
F A = A → A

data D : Set where
  c₀ : D
  c₁ : F D

f : D → String
f c₀     = "OK\n"
f (c₁ x) = f x

main = putStr (f (c₁ c₀))
