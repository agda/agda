{-# OPTIONS --safe #-}

data ⊥ : Set where

E : Set₁
E = Set where

  {-# TERMINATING #-}
  e : ⊥
  e = e

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

interleaved mutual

  {-# TERMINATING #-}
  k : ⊥
  k = k

opaque

  {-# TERMINATING #-}
  l : ⊥
  l = l

record M : Set where
  interleaved mutual
    {-# TERMINATING #-}
    m : ⊥
    m = m

record N : Set where
  opaque
    {-# TERMINATING #-}
    n : ⊥
    n = n

O : Set₁
O = Set where
  interleaved mutual
    {-# TERMINATING #-}
    o : ⊥
    o = o

  opaque
    {-# TERMINATING #-}
    o' : ⊥
    o' = o'
