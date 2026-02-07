-- Andreas, 2026-02-07, issue #8374
-- Allow fixity declarations outside of anoymous modules.

module _ where

-- This fixity declaration should also apply to the operator in the anonymous module.

module NonNest where

  infixr 20 _∷_

  module _ (A : Set) where
    data List : Set where
      [] : List
      _∷_ : A → List → List

  -- This needs the fixity to parse:

  dup : {A : Set} (a : A) → List A
  dup a = a ∷ a ∷ []

module Nest where

  infixr 20 _∷_

  module _ (A : Set) where
    B = A -- random stuff

    -- Add another layer of anonymous module
    module _ where
      data List : Set where
        [] : List
        _∷_ : A → List → List

  -- This needs the fixity to parse:

  dup : {A : Set} (a : A) → List A
  dup a = a ∷ a ∷ []

module Overwrite where

  infixl 0 _∷_

  module _ (A : Set) where
    B = A -- random stuff

    -- Add another layer of anonymous module
    module _ where
      data List : Set where
        [] : List
        _∷_ : A → List → List
      infixr 20 _∷_

  -- This needs the fixity to parse:

  dup : {A : Set} (a : A) → List A
  dup a = a ∷ a ∷ []
