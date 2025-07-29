-- Andreas, 2025-07-25, issue #5524
-- Do not ignore repeated symbol in fixity declaration.

infix 1 _&_ _&_  -- second occurrence should be highlighted

postulate
  _&_ : Set

-- Expected error: [MultipleFixityDecls]
-- Multiple fixity or syntax declarations for
-- _&_:  infix 1 (at Issue5524.agda:4.9-12)
--       infix 1 (at Issue5524.agda:4.13-16)
