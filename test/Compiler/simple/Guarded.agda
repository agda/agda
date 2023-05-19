{-# OPTIONS --guarded --no-main #-}

module Guarded where

primitive primLockUniv : Set₁

postulate Clock : primLockUniv
{-# COMPILE GHC Clock = type () #-}
