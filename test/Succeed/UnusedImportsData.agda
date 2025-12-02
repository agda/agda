-- Andreas, 2025-11-27, AIM XLI, Angers, France
-- New warning UnusedImports;
-- test the warning for some uses of data types.

{-# OPTIONS -WUnusedImports #-}

module _ (_ : Set) where

-- The following tests that we do not account uses of an A.QName
-- for the wrong open statement.

module AccountPerOpen where

  module M where
    data D : Set where
      c : D
    private x = c

  module M1 where
    open M
    -- These uses of names D and c should not account for the second "open M" below.
    D' = D
    c' = c

  module M2 where
    open M
    -- This should trigger an unused import warning:
    -- Redundant opening of M

  module M3 where
    open M using (c) renaming (D to D)
    -- This should trigger an unused import warning and highlight c.
    -- Opening M brings the following unused names into scope: c
    D' = D

  module M4 where
    open M using (c) renaming (D to D)
    -- This should trigger an unused import warning and highlight D.
    -- Opening M brings the following unused names into scope: D
    c' = c

  module M5 where
    open M using (c) renaming (D to D')
    -- This should trigger an unused import warning and highlight D.
    -- Opening M brings the following unused names into scope: D'
    c' = c

-- Test that overloaded constructors are accounted to the right open statement.

module Overloading where

  module M1 where
    data D : Set where
      c : D

  module M2 where
    data E : Set where
      c : E

  open M1
  open M2 -- Expect warning: Redundant opening of M2

  fD : D → D
  fD c = c

module Parameterized where

  module M (A : Set) where
    record R : Set where
      field
        f : A
    open R  -- Redundant opening of R
    open R public

  postulate
    A : Set

  open M A
  -- Redundant opening of UnusedImportsData.Parameterized._
