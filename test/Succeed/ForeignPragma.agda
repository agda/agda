-- Check that FOREIGN code can have nested pragmas.
module _ where

open import Common.Prelude

{-# FOREIGN GHC

{-# NOINLINE plusOne #-}
plusOne :: Integer -> Integer
plusOne n = n + 1

#-}

postulate
  plusOne : Nat → Nat

{-# COMPILE GHC plusOne = plusOne #-}
