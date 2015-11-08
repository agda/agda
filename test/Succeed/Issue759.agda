-- Andreas, 2012-11-18: abstract record values
module Issue759 where

import Common.Level

abstract
  record Wrap (A : Set) : Set where
    field wrapped : A
  open Wrap public

  wrap : {A : Set} → A → Wrap A
  wrap a = record { wrapped = a }

-- caused 'Not in Scope: recCon-NOT-PRINTED'
-- during eta-contraction in serialization

-- should work now
