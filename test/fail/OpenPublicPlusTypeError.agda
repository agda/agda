module OpenPublicPlusTypeError where

module X where

  postulate D : Set

open X public

postulate x : D

typeIncorrect : Set
typeIncorrect = Set1
