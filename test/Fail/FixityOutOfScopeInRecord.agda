{-# OPTIONS --warning=error #-}

module FixityOutOfScopeInRecord where

record R : Set where
  infixl 30 _+_

-- Should complain that _+_ is not in scope
-- in its fixity declaration.
