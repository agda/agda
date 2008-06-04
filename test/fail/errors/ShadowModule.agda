
module ShadowModule where

module A where
  module B where
    data D : Set where

open A

module B where
