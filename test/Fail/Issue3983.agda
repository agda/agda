{-# OPTIONS --safe #-}

data ⊥ : Set where

private

  {-# TERMINATING #-}
  f : ⊥
  f = f

mutual

  {-# TERMINATING #-}
  g : ⊥
  g = g

abstract

  {-# TERMINATING #-}
  h : ⊥
  h = h

record I : Set where
  {-# TERMINATING #-}
  i : ⊥
  i = i

instance

  {-# TERMINATING #-}
  j : I
  j = j
