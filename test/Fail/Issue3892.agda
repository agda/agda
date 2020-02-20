-- Andreas, 2019-07-07, issue #3892

postulate Foo : Set
data Foo where

-- WAS: internal error

-- EXPECTED:
-- Multiple definitions of Foo. Previous definition at ...
