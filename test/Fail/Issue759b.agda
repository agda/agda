
module Issue759b where

import Common.Level

abstract
  record Wrap (A : Set) : Set where
    constructor wrp
    field wrapped : A
  open Wrap public

wrap : {A : Set} → A → Wrap A
wrap a = record { wrapped = a }

-- WAS: Broken error message:

-- Not in scope:
--   Issue759b.Wrap.wrp at
-- when checking the definition of wrap

-- NOW:

-- Expected non-abstract record type, found Wrap
-- when checking that the expression record { wrapped = a } has type
-- Wrap .A
