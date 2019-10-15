-- {-# OPTIONS -v tc.meta:50 #-}
-- Andreas 2012-03-27, record pattern unification
{-# OPTIONS --irrelevant-projections #-}

module Issue376-irrelevant-projections where

open import Common.Equality
open import Common.Irrelevance

bla4 : (A : Set) ->
  let A' = Squash (Squash A) in
  let X : .(z : A') -> (C : .A' -> Set) -> (.(z : A') -> C z) -> C z
      X = _
  in  (a : A)(C : .A' -> Set)(k : .(z : A') -> C z) ->
      X (squash (squash a)) C k ≡ k (squash (squash a))
bla4 A a C k = refl
