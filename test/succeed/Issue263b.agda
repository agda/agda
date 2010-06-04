-- Datatype modules weren't added as sections properly.
module Issue263b where

module M (A : Set) where
  data D : Set where

postulate A : Set

open M.D A

-- The module M.D is not parameterized, but is being applied to
-- arguments
-- when checking the module application module _ = M.D A
