-- You can't use the names from a parameterised module without instantiating it.
module UninstantiatedModule where

module A (X : Set) where

  f : X -> X
  f x = x

g = A.f

