-- Andreas, 2020-03-19, issue #4486
-- "did you mean?" now also for invalid imports

record Foo : Set₁ where
  field Θ : Set

open Foo using () renaming (θ to unwrap)

-- EXPECTED:
-- The module Foo doesn't export the following:
--   θ (did you mean 'Θ'?)

module M where
  private postulate S : Set

open M using (S)

-- EXPECTED:
-- The module M doesn't export the following:
--   S

module N where
  module O where
    record R : Set where
  open O public using (module R)

module N' where
  module O where
    record R : Set where
  open O public hiding (module R)

open N  using (R)
open N' using (module R)

-- EXPECTED:
-- The module N doesn't export the following:
--   R
-- The module N' doesn't export the following:
--   module R

module AB where
  record Ananas : Set where

open AB using (Bananas)

-- EXPECTED:
-- The module AB doesn't export the following:
--   Bananas (did you mean 'Ananas'?)

open AB using (module Bananas)

-- EXPECTED:
-- The module AB doesn't export the following:
--   module Bananas (did you mean 'Ananas'?)
