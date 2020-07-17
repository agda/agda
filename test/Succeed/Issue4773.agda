-- Andreas, 2020-06-23, issue #4773
-- reported by gallais, originally reported on mailing list by mechvel

-- Regression in 2.5.1:
-- import directives applied to modules no longer warn
-- when private names are mentioned

-- {-# OPTIONS -v scope:40 #-}

module _ where

-- MWE:
-------

module M where
  private
    X = Set
    Y = Set
    Z = Set

module N  = M using  (X) renaming (Y to Y') hiding (Z)

-- EXPECTED: warning about X, Y, Z

-- Extended original example, using 'open M args'
-------------------------------------------------

module A (X : Set₁) where
 Y = X

module B (X : Set₁) where
  open A X using (Y)
  private Z = Set

open B Set renaming (Y to Y') renaming (Z to Z')

-- EXPECTED: warning about Y, Z

-- Y' is not in scope
-- test = Y'
