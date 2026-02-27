-- Andreas, 2026-02-27, issues #3355 and #3008:
-- Allow NO_POSITIVITY_CHECK in records and where blocks.

-- 1. Still ignored outside mutual block before non-data/record definition.
---------------------------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}     -- Useless, not attached to data/record and outside mutual block
foo : Set1
foo = Set
  where
  record R : Set where
    inductive
    field f : R → R              -- Expected positivity error here.

-- Expected warning: -W[no]InvalidNoPositivityCheckPragma
-- NO_POSITIVITY_CHECKING pragmas can only precede a data/record
-- definition or a mutual block (that contains a data/record definition).

-- Expected error: [NotStrictlyPositive]
-- R is not strictly positive, because it occurs
-- to the left of an arrow
-- in the definition of R.

-- 2. No longer ignored in `where` block.
-----------------------------------------

where1 : Set1
where1 = Set
  where
  {-# NO_POSITIVITY_CHECK #-}
  record S : Set where
    inductive
    field g : S → S              -- No positivity error here!

where2 : Set1
where2 = Set
  where
  mutual
    bar = Set
    {-# NO_POSITIVITY_CHECK #-}
    record S : Set where
      inductive
      field g : S → S              -- No positivity error here!

where3 : Set1
where3 = Set
  where
  mutual                           -- Does not help.
    record R : Set where
      inductive
      field f : R → R              -- Error here.
    {-# NO_POSITIVITY_CHECK #-}    -- Misplaced.
    bar = Set

-- Expected warning: -W[no]InvalidNoPositivityCheckPragma
-- NO_POSITIVITY_CHECKING pragmas can only precede a data/record
-- definition or a mutual block (that contains a data/record
-- definition).
-- when scope checking the declaration
--   where3 = Set
--     where
--       mutual
--         record S : Set where
--           inductive
--           field g : S → S
--         {-# NO_POSITIVITY_CHECK #-}
--         bar = Set

-- Expected error: [NotStrictlyPositive]
-- R is not strictly positive, because it occurs
-- to the left of an arrow
-- in the definition of R.

where4 : Set1
where4 = Set
  where
  {-# NO_POSITIVITY_CHECK #-}      -- Precedes a mutual block
  mutual
    bar = Set
    record S : Set where
      inductive
      field g : S → S              -- No positivity error here!

where5 : Set1
where5 = Set
  where
    record S : Set
    {-# NO_POSITIVITY_CHECK #-}
    record S where
      inductive
      field g : S → S              -- No positivity error here!

where6 : Set1
where6 = Set
  where
    {-# NO_POSITIVITY_CHECK #-}
    record S : Set
    record S where
      inductive
      field g : S → S              -- No positivity error here!

-- 3. No longer ignored in `record` declaration.
------------------------------------------------

module InRecord where
  record R : Set where
    inductive
    field f : R → R                -- Expected positivity error here.

    {-# NO_POSITIVITY_CHECK #-}
    record S : Set where
      inductive
      field g : S → S              -- But not here!

    record R' : Set where
      inductive
      field f : R' → R'            -- Expected positivity error here.

    {-# NO_POSITIVITY_CHECK #-}
    record S' : Set
    record S' where
      inductive
      field g : S' → S'            -- But not here!

-- Expected error: [NotStrictlyPositive]
-- R' is not strictly positive, because it occurs
-- to the left of an arrow
-- in the definition of R'.

-- Expected error: [NotStrictlyPositive]
-- R is not strictly positive, because it occurs
-- to the left of an arrow
-- in the definition of R.
