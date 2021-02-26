{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.cover.strategy:20 -v tc.cover.precomputed:10 #-}
-- {-# OPTIONS -v term.check.clause:25 #-}
-- {-# OPTIONS -v term.matrices:40 #-}

module DotPatternTermination where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- A simple example.
module Test1 where
  data D : Nat -> Set where
    cz : D zero
    c1 : forall n -> D n -> D (suc n)
    c2 : forall n -> D n -> D n

  -- To see that this is terminating the termination checker has to look at the
  -- natural number index, which is in a dot pattern.
  f : forall n -> D n -> Nat
  f .zero    cz        = zero
  f .(suc n) (c1  n d) = f n (c2 n d)
  f n        (c2 .n d) = f n d

-- There was a bug with dot patterns having the wrong context which manifested
-- itself in the following example.
module Test2 where
  data P : Nat -> Nat -> Set where
    c  : forall {d r} -> P d r -> P (suc d) r
    c' : forall {d r} -> P d r -> P d r

  g : forall {d r} -> P d r -> Nat
  g .{suc d} {r} (c {d} .{r} x) = g (c' x)
  g (c' _) = zero

-- Another bug where the dot patterns weren't substituted properly.
module Test3 where

  data Parser : Nat -> Set where
    alt :  (d : Nat) -> Nat -> Parser d -> Parser (suc d)
    !   :  (d : Nat) -> Parser (suc d)
    pp  :  (d : Nat) -> Parser d

  parse₀ : (d : Nat) -> Parser d -> Nat
  parse₀ .(suc d) (alt d zero p) = parse₀ d p
  parse₀ .(suc d) (alt d _ p)    = parse₀ d p
  parse₀ ._       (! d)          = parse₀ d (pp d)
  parse₀ ._       (pp d)         = zero


module Test4 where
  -- Andreas, 2016-10-01 see issue #2231
  -- abstract f sees through abstract suc, so dot pattern termination
  -- succeeds.

  abstract
    data N : Set where
      suc' : N → N

    sucN : N → N
    sucN = suc'

  data D : N → Set where
    c1 : ∀ n → D n → D (sucN n)
    c2 : ∀ n → D n → D n

  abstract
  -- To see that this is terminating the termination checker has to look at the
  -- natural number index, which is in a dot pattern.
    f : ∀ n → D n → Set
    f .(sucN n) (c1  n d) = f n (c2 n (c2 n d))
    f n         (c2 .n d) = f n d
