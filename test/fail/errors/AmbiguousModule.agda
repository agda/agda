module AmbiguousModule where

module A where
module B where
  module A where

open B
open A

