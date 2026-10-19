module AmbiguousModule where

module B where
  module A where

module A where

open B
open A
