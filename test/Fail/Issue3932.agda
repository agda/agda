-- Andreas, 2019-07-23, issue #3932
--
-- Mutual blocks are not supported in mutual blocks

module _ where

module M where

  mutual
    A : Set1
    A = Set

    mutual
      B : Set1
      B = A

module N where

  mutual
    A : Set1
    A = Set

    mutual
      A = Set

module O where

  mutual
    A : Set1

    mutual
      A = Set

-- WAS: internal errors

-- EXPECTED ERRORS:
--
-- * mutual blocks in mutual blocks are not supported
--
-- * The following names are declared but not accompanied by a definition: A
--   when scope checking the declaration
--     module O where
