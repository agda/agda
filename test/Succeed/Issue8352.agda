{-# OPTIONS --guarded --no-main #-}
-- Test that the JS backend warns about unknown primitives.
module Issue8352 where

primitive
  primLockUniv : Set₁
