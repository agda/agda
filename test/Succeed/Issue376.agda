-- {-# OPTIONS -v tc.meta:50 #-}
-- Andreas 2012-03-27, record pattern unification
module Issue376 where

import Common.Level
open import Common.Equality
open import Common.Irrelevance

record Sigma (A : Set)(B : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Sigma public

record Unit : Set where
  constructor unit

bla1 : (A : Set) (a : A) ->
  let X : Unit -> A
      X = _
  in  X unit ≡ a
bla1 A a = refl

bla2 : (A : Set)(B : A -> Set) ->
  let X : Sigma A B -> Sigma A B
      X = _
  in  (x : A)(y : B x) -> X (x , y) ≡ (x , y)
bla2 A B x y = refl
-- _55 A B (x , y) := (x , y)

-- irrelevant records
bla3 : (A : Set)(B : A -> Set) ->
  let X : .(z : Sigma A B) -> (C : .(Sigma A B) -> Set) -> (.(z : Sigma A B) -> C z) -> C z
      X = _
  in  (x : A)(y : B x)(C : .(Sigma A B) -> Set)(k : .(z : Sigma A B) -> C z) ->
      X (x , y) C k ≡ k (x , y)
bla3 A B x y C k = refl

-- nested irrelevance
-- Jesper, 2019-10-15: This constructs the solution
-- `X := \z C k → k (squash (squash (unsquash (unsquash a))))`
-- which is invalid unless --irrelevant-projections is enabled.
--bla4 : (A : Set) ->
--  let A' = Squash (Squash A) in
--let X : .(z : A') -> (C : .A' -> Set) -> (.(z : A') -> C z) -> C z
--      X = _
--  in  (a : A)(C : .A' -> Set)(k : .(z : A') -> C z) ->
--      X (squash (squash a)) C k ≡ k (squash (squash a))
--bla4 A a C k = refl

-- projected bound var
bla5 : (A : Set) (B : A -> Set) ->
  let X : (x : A) (y : B x) -> Sigma A B
      X = _
  in  (z : Sigma A B) -> X (fst z) (snd z) ≡ z
bla5 A B z = refl

-- projected bound var
bla6 : (A : Set) (B : A -> Set) ->
  let X : A -> A
      X = _
  in  (z : Sigma A B) -> X (fst z) ≡ fst z
bla6 A B z = refl
