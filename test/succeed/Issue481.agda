-- Andreas, 2012-10-18 wish granted
module Issue481 where

-- Use case:

open import Common.Issue481ParametrizedModule Set using () renaming (id to idSet)
open import Common.Issue481ParametrizedModule (Set → Set) using () renaming (id to idSetToSet)

open import Common.Issue481ParametrizedModule

-- With 'as' clause:

open import Common.Issue481ParametrizedModule Set as PSet using (id)

{- MEANS:
import Common.Issue481ParametrizedModule
private open module PSet = Common.Issue481ParametrizedModule Set using (id)
-}

-- Abuse case:

as = Set

open import Common.Issue481ParametrizedModule as as as
module M = as

-- Test case:

module Test where

  -- should succeed:
  open import Issue481Record as Rec

  open Issue481Record

{- Note: this is NOT equivalent to the following, failing sequence

import Issue481Record
open module Rec = Issue481Record

open Issue481Record
-- Ambiguous module name Issue481Record. It could refer to any one of
--   Rec.Issue481Record
--   Issue481Record

It is equivalent to:
-}

module Test2 where

  import Issue481Record
  private
    open module Rec = Issue481Record


