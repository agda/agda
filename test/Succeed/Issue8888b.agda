-- Issue #8888: the problem does not depend on --double-check,
-- since with-abstraction checks terms internally as well.

{-# OPTIONS --cohesion --flat-split --erasure --polarity #-}

module Issue8888b where

open import Agda.Builtin.Bool

postulate
  b : Bool

record R : Set₁ where
  constructor r
  field A : Set

-- Cohesion.

postulate
  P : R → Set

flat : (@♭ x : R) → P x → P x
flat (r a) q with b
... | _ = q

flatAs : (@♭ x : R) → P x → P x
flatAs x@(r a) q with b
flatAs x@(r a) q | _ = q

-- Erasure.

data Q (@0 x : R) : Set where
  q : Q x

erased : (@0 x : R) → Q x → Q x
erased x@(r a) y with b
erased x@(r a) y | _ = y

-- Polarity.

data D : Set₁ where
  c : @+ Set → D

postulate
  T : D → Set

positive : (x : D) → T x → T x
positive (c a) t with b
... | _ = t
