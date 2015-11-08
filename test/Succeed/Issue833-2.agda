module Issue833-2 where

-- Arbitrary data type
record unit : Set where
  instance constructor tt

module Test ⦃ m : unit ⦄ { n : unit } where

open Test { tt }

