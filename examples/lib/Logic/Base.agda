
module Logic.Base where

infix 60 ¬_
infix 30 _/\_
infix 20 _\/_

data True : Set where
  tt : True

data False : Set where

elim-False : {A : Set} -> False -> A
elim-False ()

data _/\_ (P Q : Set) : Set where
  /\-I : P -> Q -> P /\ Q

data _\/_ (P Q : Set) : Set where
  \/-IL : P -> P \/ Q
  \/-IR : Q -> P \/ Q

elimD-\/ : {P Q : Set}(C : P \/ Q -> Set) ->
	   ((p : P) -> C (\/-IL p)) ->
	   ((q : Q) -> C (\/-IR q)) ->
	   (pq : P \/ Q) -> C pq
elimD-\/ C left right (\/-IL p) = left p
elimD-\/ C left right (\/-IR q) = right q

elim-\/ : {P Q R : Set} -> (P -> R) -> (Q -> R) -> P \/ Q -> R
elim-\/ = elimD-\/ (\_ -> _)

¬_ : Set -> Set
¬ P = P -> False

data ∃ {A : Set}(P : A -> Set) : Set where
  ∃-I : (w : A) -> P w -> ∃ P

∏ : {A : Set}(P : A -> Set) -> Set
∏ {A} P = (x : A) -> P x

