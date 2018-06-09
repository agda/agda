module Issue939 where

record Sigma (A : Set)(P : A → Set) : Set where
  field
    fst : A
    .snd : P fst
open Sigma

postulate
  A : Set
  P : A → Set
  x : A
  .p : P x

ex : Sigma A P
ex = record
       { fst = x
       ; snd = p
       }

-- Note: we do not need --irrelevant-projections to use them on the lhs.
ex' : Sigma A P
fst ex' = x
snd ex' = p

-- WAS: Giving p yields the following error:
-- Identifier p is declared irrelevant, so it cannot be used here
-- when checking that the expression p has type P (fst ex')

-- Fixed.  Andreas, 2013-11-05
