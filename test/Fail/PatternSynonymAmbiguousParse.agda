module PatternSynonymAmbiguousParse where

data X : Set where
  if_then_else_ : X -> X -> X -> X
  if_then_      : X -> X -> X
  x             : X

pattern bad x = if x then if x then x else x
