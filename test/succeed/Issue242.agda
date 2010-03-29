{-# OPTIONS --allow-unsolved-metas #-}
module Issue242 where

postulate Y : Set

module Inner (X : Set) where

  module M (A : Set) where
    postulate R : Set

    module R (r : R) where
      postulate C : Set

  open module MX = M Y

  module M' (r : R) where
    open module Rr = R r

    c : C
    c = {!!}
