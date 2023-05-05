-- This test case is based on a bug report submitted by Xia Li-yao.
--
-- The test case does not require the use of --erased-matches, but is
-- still handled incorrectly by Agda 2.6.2.2 (if --erasure is
-- removed).

{-# OPTIONS --without-K --erasure #-}

module Issue6413-2 where

open import Agda.Builtin.Bool
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

postulate
  print : Bool → IO ⊤

{-# FOREIGN GHC
      import qualified Data.Char
  #-}
{-# COMPILE GHC print = putStrLn . map Data.Char.toLower . show #-}
{-# COMPILE JS  print =
      x => cb => { process.stdout.write(x.toString() + "\n"); cb(0); }
  #-}

record D (A : Set) : Set where
  constructor c
  field
    x : ⊤
    y : A

f : @0 D (D ⊤) → Bool
f (c _ (c _ _)) = true

main : IO ⊤
main = print (f (c tt (c tt tt)))
