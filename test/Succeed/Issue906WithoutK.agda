{-# OPTIONS --cubical-compatible #-}

-- Andreas, 2020-02-07, instances of #906 needing --cubical-compatible to throw
-- off the termination checker.

module Issue906WithoutK where

module Issue3081 where

  postulate
    X : Set
    P : (x : X) → Set
    any : {X : Set} → X

  record W : Set where
    field
      x : X
      p : P x

  record Category : Set₁ where
    field
      z : W
      s : W → W

  {- Termination checking failed for the following functions:
       functor
     Problematic calls:
       W.x (functor .Category.s u)
       W.x (functor .Category.z)
  -}
  functor : Category
  functor .Category.z .W.x = any
  functor .Category.z .W.p = any
  functor .Category.s u .W.x = any
  functor .Category.s u .W.p = any

module Issue3081Ulf where

  open import Agda.Builtin.Nat

  record R : Set where
    field
      a : Nat
      b : Nat

  record S : Set where
    field
      r : R  -- works if we give r and h the same number of arguments
      h : Nat → R

  open R
  open S

  f : S
  f .r   .a = 0
  f .r   .b = f .r   .a
  f .h n .a = n
  f .h n .b = f .h n .a


-- Should all pass the termination checker.
