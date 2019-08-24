{-# OPTIONS --safe #-}

data ⊥ : Set where

private

  {-# TERMINATING #-}
  f : ⊥
  f = f

mutual

  {-# TERMINATING #-}
  g : ⊥
  g = f

abstract

  {-# TERMINATING #-}
  h : ⊥
  h = f

record I : Set where
  {-# TERMINATING #-}
  i : ⊥
  i = f

instance

  {-# TERMINATING #-}
  j : I
  j = j
