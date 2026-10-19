module M where

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}

main : IO ⊤
main = putStrLn "B"
