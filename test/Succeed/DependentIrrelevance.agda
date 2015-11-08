-- Andreas, AIM XIII, 2011-04-07
-- {-# OPTIONS -v tc.rec.proj:50 #-}
module DependentIrrelevance where

open import Common.Irrelevance

ElimSq = {A : Set}(P : Squash A -> Set)
         (ih : .(a : A) -> P (squash a)) ->
         (a- : Squash A) -> P a-
elimSq : ElimSq
elimSq P ih (squash a) = ih a

elimSq' : ElimSq
elimSq' P ih a- = ih (Squash.unsquash a-)

ElimSq' = {A : Set}(P : Squash A -> Set)
          (ih : forall .a -> P (squash a)) ->
          (a- : Squash A) -> P a-

record Union (A : Set)(B : .A -> Set) : Set where
  field
    .index : A
    elem   : B index

makeUnion : {A : Set}{B : .A -> Set}.(index : A)(elem : B index) -> Union A B
makeUnion i e = record { index = i ; elem = e }


{- extended parsing examples (do not work yet)

postulate
  A : Set
  P : .A -> Set
  a : A

f1 : _
f1 = λ .x -> P x

f2 : .A -> A
f2 = λ x -> a

postulate
  g   : forall .x -> P x
  f   : (.x : A) -> P x
  f'  : .(x : A) -> P x
  f'' : forall .x .(y : A) -> P x
  g1  : forall .(x y : A) -> P x
  g2  : forall (.x .y : A) -> P x
  g3  : forall {.x .y : A} -> P x
  g4  : forall x1 {.x2} .{x3 x4} {.x y} -> P x

-}
