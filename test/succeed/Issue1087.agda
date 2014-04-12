-- Andreas, 2014-04-12, Order of declaration mattered in the presence
-- of meta variables involving sizes
-- {-# OPTIONS -v tc.meta:10 -v tc.meta.assign:10 #-}

-- Error persists without option sized-types
{-# OPTIONS --sized-types #-}
module _ where

open import Common.Size
-- different error if we do not use the built-ins (Size vs Size<)

module Works where
  mutual

    data Colist' i : Set where
      inn  : (xs : Colist i) → Colist' i

    record Colist i : Set where
      coinductive
      field out : ∀ {j : Size< i} → Colist' j

module Fails where
  mutual

    record Colist i : Set where
      coinductive
      field out : ∀ {j : Size< i} → Colist' j

    data Colist' i : Set where
      inn  : (xs : Colist i) → Colist' i

-- Error: Issue1087.agda:21,45-46
-- Cannot instantiate the metavariable _20 to solution (Size< i) since
-- it contains the variable i which is not in scope of the
-- metavariable or irrelevant in the metavariable but relevant in the
-- solution
-- when checking that the expression j has type _20

-- Works now.
