
-- Run with --proof-irrelevance to produce the error.
module PropMustBeSingleton where

data (\/)(P,Q:Prop) : Prop where
  orI1 : P -> P \/ Q
  orI2 : Q -> P \/ Q

