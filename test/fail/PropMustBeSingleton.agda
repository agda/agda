{-# OPTIONS --proof-irrelevance #-}

module PropMustBeSingleton where

data _\/_ (P Q : Prop) : Prop where
  orI1 : P -> P \/ Q
  orI2 : Q -> P \/ Q

