module Issue8898 where

open import Agda.Builtin.Float
open import Agda.Builtin.Int
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.IO
open import Agda.Builtin.String

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text.IO as T #-}
{-# FOREIGN GHC import qualified System.IO #-}
{-# COMPILE GHC putStrLn = \ s -> T.putStrLn s >> System.IO.hFlush System.IO.stdout #-}
{-# COMPILE JS putStrLn = function (x) { return function(cb) { process.stdout.write(x + "\n"); cb(0); }; } #-}

-- Haskell's decodeFloat 0.0 is (0, 0). Checking this equation requires
-- the type checker to evaluate primFloatDecode 0.0.
test : primFloatDecode 0.0 ≡ just (pos 0 , pos 0)
test = refl

showInt : Int → String
showInt (pos n)    = primShowNat n
showInt (negsuc n) = primStringAppend "-" (primShowNat (suc n))

showDecode : Float → String
showDecode x with primFloatDecode x
... | just (m , e) = primStringAppend (showInt m) (primStringAppend " * 2^" (showInt e))
... | nothing      = "nothing"

main : IO ⊤
main = putStrLn (primStringAppend "decode 0.0 = " (showDecode 0.0))
