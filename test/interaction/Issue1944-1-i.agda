-- Andreas, AIM XXIII 2016-04-21 Overloaded projections

-- Milestone 1: Check overloaded projections on rhs (without postponing).

{-# OPTIONS --allow-unsolved-metas #-}

module _ (A : Set) (a : A) where

record R B : Set where
  field f : B
open R

record S B : Set where
  field f : B
open S

r : R A
R.f r = a

s : S A
S.f s = f r

t : R A → S A
S.f (t r) = f r

u : _
u = f s

-- interactive

hole0 : A
hole0 = {! f s !}  -- normalize me

hole1 = {!λ r → f (t r)!} -- normalize me
