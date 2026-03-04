-- {-# OPTIONS -v scope:20 #-}

module _ (X : Set) where

postulate
  X₁ X₂ : Set

data D : Set where
  d : D

module Q (x : D) where
    module M1 (z : X₁) where
      g = x
    module M2 (y : D) (z : X₂) where
      h = y
      open M1 public

-- module Qd = Q d

-- This fails to apply g to d!
module QM2d = Q.M2 d d

module QM2p (x : D) = Q.M2 x x

test-h : X₂ → D
test-h = QM2d.h

test-g₁ : X₂ → X₁ → D
test-g₁ = QM2d.g

test-g₂ : D → X₂ → X₁ → D
test-g₂ = QM2p.g

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

postulate
  Lift : Nat → Set
  mkLift : ∀ n → Lift n

module TS (T : Nat) where
  module Lifted (lift : Lift T) where
    postulate f : Nat

record Bla (T : Nat) : Set₁ where

  module TST = TS T
  module LT = TST.Lifted (mkLift T)

  Z : Nat
  Z = LT.f

postulate
  A : Set

module C (X : Set) where
  postulate cA : X

module C′  = C
module C′A = C′ A

dA' : A → A
dA' x = C′A.cA

postulate
  B : Set

module TermSubst (X : Set) where
  module Lifted (Y : Set) where
    f : Set
    f = Y

record TermLemmas (Z : Set) : Set₁ where
  module TZ  = TermSubst A
  module TZL = TZ.Lifted B
  foo : Set
  foo = TZL.f
  field Y : Set

module NatCore where
  module NatT (X Y : Set) where
    Z : Set
    Z = X → Y

module NatTrans (Y : Set) where
  open NatCore public

module NT = NatTrans

foo : Set → Set
foo X = Eta.Z X → Eta′.Z X
  module Local where
    module Eta = NT.NatT X X
    -- equivalent to
    module Eta′ (Y : Set) = NT.NatT X X Y
