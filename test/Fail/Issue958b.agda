
module _ where

open import Imports.Issue958

-- Extra parameterised module to make sure checkpoints line up with
-- the checkpoints in the imported module.
module Dummy (X : Set) where

module M (_ fun : IsFunctor) where

  open IsFunctor

  -- Here we're in the "same" checkpoint as when the display form was
  -- created. It's not the same though, so the display form should be
  -- generalized and lifted to the appropriate context.
  test : map fun
  test = fun

  -- EXPECTED: IsFunctor !=< map fun
