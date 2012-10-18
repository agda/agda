-- Andreas, 2012-10-18
module Issue481 where

as = Set

-- we do not support mixing of module arguments with 'as' clause
open import Common.Issue481ParametrizedModule as as -- OK, as clause
open import Common.Issue481ParametrizedModule as as as -- NOT OK, mix


