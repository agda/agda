{-# OPTIONS --warning=error #-}

module FixityOutOfScopeInRecord1 where

postulate _+_ : Set

record R : Set where
  infixl 30 _+_

-- Should complain that _+_ is not in (the same) scope
-- in (as) its fixity declaration.
