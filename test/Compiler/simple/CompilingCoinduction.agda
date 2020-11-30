
module CompilingCoinduction where

open import Common.Coinduction
open import Common.Char
open import Common.String

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () (()) #-}

postulate
  IO : Set → Set

{-# COMPILE GHC IO = type IO #-}
{-# BUILTIN IO IO #-}

{-# FOREIGN GHC import qualified Data.Text.IO #-}

postulate
  putStrLn : ∞ String → IO Unit

{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn . MAlonzo.RTE.flat #-}
{-# COMPILE JS  putStrLn = function(x) { return function(cb) { process.stdout.write(x.flat() + "\n"); cb(0); }; } #-}

main = putStrLn (♯ "a")
