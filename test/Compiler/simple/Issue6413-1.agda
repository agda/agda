-- This test case is based on a bug report submitted by Xia Li-yao.

{-# OPTIONS --without-K --erasure --erased-matches #-}

module Issue6413-1 where

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

data D (A : Set) : Set where
  c : ⊤ → A → D A

f : @0 D (D ⊤) → Bool
f (c _ (c _ _)) = true

main : IO ⊤
main = print (f (c tt (c tt tt)))
