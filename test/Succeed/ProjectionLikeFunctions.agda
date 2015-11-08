-- Getting projection like functions right was a little tricky.
-- Here are the cases that didn't work and weren't caught by
-- existing test cases.
module ProjectionLikeFunctions where

record Wrap (A : Set) : Set where
  constructor [_]
  field unwrap : A

postulate
  Nat   : Set
  n     : Nat
  Thm   : Nat → Set
  prf   : ∀ n → Thm n

module M x (p : Thm x) (w : Wrap Nat) where
  module W = Wrap w

module M′ = M n (prf n) ([ n ])

test₁ : Thm M′.W.unwrap
test₁ = prf n

eq! : ∀ x (S : Thm x) → Wrap Nat → Nat
eq! s S [n] = W.unwrap
  module Local where
    module W = Wrap [n]

test₂ : Thm (eq! n (prf n) [ n ])
test₂ = prf n
