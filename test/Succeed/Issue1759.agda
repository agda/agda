-- Andreas, 2016-01-03, issue reported by mechvel
module _ where

-- With hidden parameter, things work

module Works0 {A : Set} where

  postulate
    P : (a : A) → Set

  record Works (a : A) : Set where

    f : P a → Set
    f p with p
    ... | _ = A

-- With visible parameter, the error is triggered
-- because it is turned hidden inside the record section

module Fails (A : Set) where

  postulate
    P : (a : A) → Set

  -- Modules do not touch visibility of parameters, so things work.
  module Works (a : A) where

    f : P a → Set
    f p with p
    ... | _ = A

  -- Records have some magic to make record parameters hidden
  -- in record section.
  -- This leads to an error in @checkInternal@.

  record Fails (a : A) : Set where

    f : P a → Set
    f p with p
    ... | _ = A

-- ERROR WAS:
-- Expected a visible argument, but found a hidden argument
-- when checking that the type (w p : P a) → Set of the
-- generated with function is well-formed

-- Should succeed.
