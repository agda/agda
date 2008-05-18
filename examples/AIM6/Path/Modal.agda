
module Modal where

open import Prelude
open import Star

data Progress (A : Set) : Set where
  cont : A -> Progress A
  stop : Progress A

record Some {A : Set}(R : Rel A) : Set where
  field
    a    : A
    b    : A
    edge : R a b

some : {A : Set}{R : Rel A}{a b : A} -> R a b -> Some R
some x = record {a = _; b = _; edge = x}

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

mapAny : {A₁ A₂ : Set}{R₁ : Rel A₁}{R₂ : Rel A₂}
         {P₁ : EdgePred R₁}{P₂ : EdgePred R₂}{a b : A₁}{xs : Star R₁ a b}
         {i : A₁ -> A₂}{f : R₁ =[ i ]=> R₂} ->
         ({a b : A₁}{x : R₁ a b} -> P₁ x -> P₂ (f x)) ->
         Any P₁ xs -> Any (\{a b} -> P₂{a}{b}) (map i f xs)
mapAny h (step   • i) = step • mapAny h i
mapAny h (done p • ε) = done (h p) • ε
mapAny h (done p • (() • _))

data Check {A : Set}{R : Rel A}(P : EdgePred R) :
           Rel (Some (Star R)) where
  check : {a b c : A}{x : R a b}{xs : Star R b c} ->
          P x -> Check P (some (x • xs)) (some xs)

checkedEdge : {A : Set}{R : Rel A}{P : EdgePred R}{xs ys : Some (Star R)} ->
              Check P xs ys -> Some R
checkedEdge (check {x = x} _) = some x

uncheck : {X : Set}{R : Rel X}{P : EdgePred R}{xs ys : Some (Star R)}
          (chk : Check P xs ys) -> P (Some.edge (checkedEdge chk))
uncheck (check p) = p

All : {A : Set}{R : Rel A}(P : EdgePred R) -> EdgePred (Star R)
All P {a}{b} xs = Star (Check P) (some xs) (some {a = b} ε)

data Lookup {A : Set}{R : Rel A}(P Q : EdgePred R) : Set where
  result : {a b : A} -> (x : R a b) -> P x -> Q x -> Lookup P Q

lookup : {A : Set}{R : Rel A}{P Q : EdgePred R}{a b : A}{xs : Star R a b} ->
         Any P xs -> All Q xs -> Lookup (\{a b} -> P{a}{b}) Q
lookup (step   • i) (check _ • xs) = lookup i xs
lookup (done p • ε) (check q • _ ) = result _ p q
lookup (done p • (() • _)) (check q • _ )
