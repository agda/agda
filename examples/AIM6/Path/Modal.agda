
module Modal where

open import Prelude
open import Star

data Progress (A : Set) : Set where
  cont : A -> Progress A
  stop : Progress A

data Some {A : Set}(R : Rel A) : Set where
  some : {a b : A} -> R a b -> Some R

EdgePred : {A : Set} -> Rel A -> Set1
EdgePred R = forall {a b} -> R a b -> Set

data PStep {A : Set}{R : Rel A}(P : EdgePred R) :
           Rel (Progress (Some (Star R))) where
  step : {a b c : A}{x : R a b}{xs : Star R b c} ->
         PStep P (cont (some (x • xs))) (cont (some xs))
  done : {a b c : A}{x : R a b}{xs : Star R b c} ->
         P x -> PStep P (cont (some (x • xs))) stop

Any : {A : Set}{R : Rel A}(P : EdgePred R) -> EdgePred (Star R)
Any P xs = Star (PStep P) (cont (some xs)) stop

data Check {A : Set}{R : Rel A}(P : EdgePred R) :
           Rel (Some (Star R)) where
  check : {a b c : A}{x : R a b}{xs : Star R b c} ->
          P x -> Check P (some (x • xs)) (some xs)

All : {A : Set}{R : Rel A}(P : EdgePred R) -> EdgePred (Star R)
All P {a}{b} xs = Star (Check P) (some xs) (some {a = b} ε)