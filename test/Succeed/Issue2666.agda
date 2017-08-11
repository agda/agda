
module _ where

module G where
  module H where

module A where
  module B where
    module C where
      open G public

module I = A.B.C.H
