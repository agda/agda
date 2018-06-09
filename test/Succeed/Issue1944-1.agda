-- Andreas, AIM XXIII 2016-04-21 Overloaded projections

-- Milestone 1: Check overloaded projections on rhs (without postponing).

module _ (A : Set) (a : A) where

module RecDefs where

  record R (B : Set) : Set where
    field f : B
  open R public

  record S (B : Set) : Set where
    field f : B
  open S public

  record T (B : Set) : Set where
    field f : B → B
  open T public

open RecDefs public

r : R A
R.f r = a

s : S A
S.f s = f r

t : R A → S A
S.f (t r) = f r

u : _
u = f s

v = f s

w : ∀{A} → T A → A → A
w t x = f t x
