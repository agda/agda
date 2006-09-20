{-# OPTIONS --proof-irrelevance #-}

module proofIrr where

data True : Prop where
  tt : True

data _ /\ _ (P,Q:Prop) : Prop where
  /\I : P -> Q -> P /\ Q

irrelevant : {P:Prop} -> (F : P -> Set) -> (p,q:P) -> F p -> F q
irrelevant F p q fp = fp

