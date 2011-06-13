module InstanceArgumentsBraces where

record T' : Set where

record T'' : Set where
  field a : T'

testT'' : T''
testT'' = record { a = record {}}
