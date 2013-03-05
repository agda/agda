-- {-# OPTIONS -v tc.cover.splittree:10 -v tc.cc.splittree:10  #-}
module Issue106 where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

_+_ : ℕ -> ℕ -> ℕ
zero + m = m
suc n + m = suc (n + m)

record ⊤ : Set where

data C : ℕ -> Set where
  c : C 0

data D : Set where
  d : forall s (x : C s) (xs : D) -> D

f : D -> ℕ -> ⊤
f (d zero c x) (suc n) = f (d 0 c x) n
f (d .zero c x) n      = f x (suc n)

g : D -> ℕ -> ⊤
g (d .zero c x) (suc n) = g (d zero c x) n
g (d .zero c x) n       = g x (suc n)

h : D -> ℕ -> ⊤
h (d .zero c x) (suc n) = h (d 0 c x) n
h (d .zero c x) n       = h x (suc n)
