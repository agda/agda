-- Check that FOREIGN code can have nested pragmas.
module _ where

open import Common.Prelude

{-# FOREIGN GHC

{-# NOINLINE plusOne #-}
plusOne :: Integer -> Integer
plusOne n = n + 1

{-# INLINE plusTwo #-}
plusTwo :: Integer -> Integer
plusTwo = plusOne . plusOne

#-}

postulate
  plusOne : Nat → Nat

{-# COMPILE GHC plusOne = plusOne #-}
