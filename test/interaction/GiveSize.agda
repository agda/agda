-- {-# OPTIONS -v tc.meta:30 #-}

module GiveSize where

{-# BUILTIN SIZE Size #-}

postulate
  A : Size → Set
  c : ∀ i → A i

k : ∀ i → A i
k i = c {!i!}
