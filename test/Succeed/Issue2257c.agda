-- Andreas, 2026-11-05, issue #2257
-- Interaction metas are reused when a record declaration is rechecked
-- for the record module.  The reused meta needs to be well-typed.

{-# OPTIONS --allow-unsolved-metas --double-check #-}

-- Hole in type position under binders that are not the record variable.

record Binders : Set₁ where
  foo : Set₁
  foo = (f : Set) (x : f) → {!!}

  field
    bar : Set

-- Field named like the record variable.

record FieldNamedLikeRecordVar : Set₁ where
  field
    r : Set

  foo : Set₁
  foo = Set → {!!}

  field
    bar : Set

-- Parameters and fields in the context of the meta,
-- to be replaced by projections from the record variable.

record ParamsAndFields (A : Set) : Set₁ where
  field
    a : A
    F : ∀ {f} → Set

  foo : Set
  foo = ∀ {f} → {!!}

  field
    bar : Set

-- Hole as type of a definition, with nothing else determining its sort.

record HoleAsType : Set₁ where
  foo : {!!}
  foo = {!!}

  field
    bar : Set

-- Other definitions before the hole, and fields in between holes.

record Definitions (A : Set) : Set₁ where
  field
    a : A

  foo : Set
  foo = A

  baz : Set → Set
  baz X = ∀ {f} → {!!}

  field
    bar : Set

  qux : Set₁
  qux = ∀ {g} → g → {!!}

-- Hidden variable bound by the left-hand side and named like an earlier field.

record HiddenNamedLikeField (A : Set) : Set₁ where
  field
    a : A

  foo : {a : A} → Set
  foo = {!!}

  field
    bar : Set

-- Hidden variables are bound by the left-hand side in the second pass.
-- In the first pass, they are lambda-bound if the body is not a hole,
-- and otherwise part of the type of the hole.

record HiddenFromLeftHandSide (A : Set) : Set₁ where
  foo : A → {b : A} {c : A} → Set₁
  foo x = Set → {!!}

  baz : A → {b : A} {c : A} → Set
  baz x = {!!}

  field
    bar : Set

-- Variable bound by the left-hand side and named like a later field.

record VariableNamedLikeLaterField (A : Set) : Set₁ where
  field
    a : A

  foo : (b : A) → Set₁
  foo b = Set → {!!}

  field
    b : Set
