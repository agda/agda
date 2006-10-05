-- Operators used in the wrong way.
module NoParseForApplication where

postulate
  X : Set
  _! : X -> X

right : X -> X
right x = x !

wrong : X -> X
wrong x = ! x

