-- Andreas, 2026-09-03, issue #8725, found in the agda-categories library.
--
-- When a module application copies a proper projection or a constructor,
-- the respective record/data type has to be copied as well (see #8037).
-- The copy of the type has to be placed in the correct module: a record
-- type lives one level above its projections (which live in the record
-- module), whereas a data type lives in the same module as its constructors.
--
-- The generated constructor of a record without a constructor declaration
-- lives in the record module, so it must not be used to place the copy of
-- the record type in the same module: otherwise the copy of the record type
-- ends up inside a record module, whose telescope has one parameter too many
-- (the record value).  The next module application copying this record type
-- then crashed with an internal error in 'piApply'.

module Issue8725 where

postulate A : Set

module M (X : Set) where

  record R : Set where
    field f : X

-- Export only the record module R, not the record type R.
-- Thus, the copy of the record type below has to be invented by Agda.

module Core where
  open M A public using (module R)

module C = Core

postulate r : M.R A

-- This module application crashed.

module r = C.R r

test : A
test = r.f
