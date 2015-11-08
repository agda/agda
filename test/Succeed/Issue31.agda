
-- There was a bug with the open M es syntax.
module Issue31 where

record M : Set1 where
  field
    A : Set

module MOps (m : M) where
  open M m public

postulate m : M

open MOps m hiding (A)
open MOps m using (A)

postulate foo : A -> Set

module AnotherBug where

  postulate Z : Set

  module A (X : Set) where
    postulate H : Set
  module B (Y : Set) where

  module C where
    open A Z
    open B Z public

  postulate H : Set
  open C

  X = H

