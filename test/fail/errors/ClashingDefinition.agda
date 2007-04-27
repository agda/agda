-- You can't use the same name more than once in the same scope.
module ClashingDefinition where

postulate
  X : Set
  X : Set

Y = X

