-- Check if sharing is properly used for evaluation.
-- E.g. (\x -> putStrLn x; putStrLn x) (computeString)
-- should only evaluate computeString once.
-- Doing the evaluation twice should still yield the correct result,
-- but will incur a performance penalty.

-- MAlonzo: seems to use proper sharing for this example with ghc -O,
-- but not with ghc -O0. The sharing for -O0 is not introduced by MAlonzo,
-- but by the cleverness of GHC.

module Sharing where

open import Common.Prelude
open import Common.IO

{-# FOREIGN GHC import qualified Debug.Trace #-}

postulate
  primTrace : {b : Set} → String → b → b
{-# COMPILE GHC primTrace = \ _ -> Debug.Trace.trace #-}

main : IO Unit
main = (λ x → putStrLn x ,, putStrLn x ) (primTrace "Eval" "hoi")

