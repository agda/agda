
module Logic where

data True : Set where
  tt : True

infix 10 _/\_

data _/\_ (P Q : Set) : Set where
  <_,_> : P -> Q -> P /\ Q

