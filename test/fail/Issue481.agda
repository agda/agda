-- Andreas, 2012-10-18
module Issue481 where

as = Set

open import Common.Issue481ParametrizedModule as as -- as clause
open import Common.Issue481ParametrizedModule as as as -- as clause, duplicate def.



