
module AmbiguousName where

module A where
  postulate X : Set

module B where
  module A where
    postulate X : Set

open A renaming (X to Y)
open B

Z = A.X
