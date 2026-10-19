{-# OPTIONS --erasure #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

postulate
  exitFailure exitSuccess : IO ⊤

{-# FOREIGN GHC import System.Exit qualified as Exit #-}
{-# COMPILE GHC exitFailure = Exit.exitFailure #-}
{-# COMPILE GHC exitSuccess = Exit.exitSuccess #-}
{-# COMPILE JS exitFailure = function(cb) { process.exit(1); } #-}
{-# COMPILE JS exitSuccess = function(cb) { process.exit(0); } #-}

data ENat : Set where
  z    : ENat
  @0 s : ENat → ENat

data GE2 : ENat → Set where
  swap : (@0 n : _) → GE2 (s (s n))

snot : ∀ {@0 n} → GE2 n → Bool → Bool
snot {n = s (s n)} (swap n) false = true
snot {n = s (s n)} (swap n) true  = false

test : Bool → IO ⊤
test false = exitSuccess
test true  = exitFailure

main : IO ⊤
main = test (snot (swap z) true)
