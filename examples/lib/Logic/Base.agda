
module Logic.Base where

infix 60 ¬_
infix 30 _/\_
infix 20 _\/_

data True : Set where
  tt : True

data False : Set where

data _/\_ (P, Q : Set) : Set where
  /\-I : P -> Q -> P /\ Q

data _\/_ (P, Q : Set) : Set where
  \/-IL : P -> P \/ Q
  \/-IR : Q -> P \/ Q

¬_ : Set -> Set
¬ P = P -> False

data Exist {A : Set}(P : A -> Set) : Set where
  exist-I : (w : A) -> P w -> Exist P

Forall : {A : Set}(P : A -> Set) -> Set
Forall {A} P = (x : A) -> P x

