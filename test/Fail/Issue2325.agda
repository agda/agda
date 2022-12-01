
postulate
  X A : Set

module Foo {{x : X}} where

  postulate
    B C : Set
    foo : A → B → C → Set

module Bar {{x : X}} where
  open Foo

  postulate
    -- The following fails to infer the instance argument if we do not either:
    --   * apply {{x}} explicitly to foo
    --   * apply {{x}} explicitly when opening module Foo
    --   * define fail1 in module Foo
    fail1 : ∀ {a b b' c c'} → foo a b c → foo a b' c'

    -- However, the following works
    work1 : ∀ {a b c} → foo a b c → foo a b c
    work2 : ∀ {a a' b c} → foo a b c → foo a' b c
    work3 : ∀ {a b b' c} → foo a b c → foo a b' c
    work4 : ∀ {a a' b b' c} → foo a b c → foo a' b' c
    work5 : ∀ {a b c c'} → foo a b c → foo a b c'
    work6 : ∀ {a a' b c c'} → foo a b c → foo a' b c'
    work7 : ∀ {a a' b b' c c'} → foo a b c → foo a' b' c'

data Nat : Set where
  suc : Nat → Nat
  instance
    zero : Nat

instance
  one = suc zero

data IsSuc : Nat → Set where
  isSuc : ∀{n} → IsSuc (suc n)

postulate
  F : {{x : Nat}} (p : IsSuc x) → Set

test = F isSuc  -- yellow, but should not be
