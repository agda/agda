
module Issue152 where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

f : ℕ → ℕ
f 0 with zero
f 0 | n = n
f 1 with zero
f 1 | n = n
f n = n

g : ℕ → ℕ
g 0    with zero
g zero | n = n
g 1    with zero
g (suc zero) | n = n
g n = n

h : ℕ → ℕ
h zero with zero
h 0    | n = n
h (suc zero) with zero
h 1 | n = n
h n = n

