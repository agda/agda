-- Andreas, 2026-08-27, issue #8687, reported by @bdrisc-ant
--
-- When a definition by copattern matching omits an instance field,
-- the coverage checker infers the missing clause by running instance
-- search in the telescope of the split clause, under the module
-- parameter substitutions ("checkpoints") of the definition site.
-- These need to be weakened into that telescope.
--
-- Agda used to weaken them by the arity of the function minus the
-- number of parameters of the module the function lives in, which is
-- only correct if the function was created over exactly the telescope
-- of its module.  The auxiliary function of a copattern
-- pattern-lambda is created over the whole context at the lambda, so
-- its checkpoints were shifted too far to the left: instance search
-- then elaborated the instances of the module against the wrong
-- variables, or Agda crashed.
--
-- Below, the field `.P.i` is always omitted and thus inferred by
-- instance search; each `check` verifies that the inferred instance is
-- the correct one.  Before the fix, each of these variants made Agda
-- crash.  See test/Fail/Issue8687.agda for a variant that was unsound.

{-# OPTIONS --safe #-}

module Issue8687 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record C : Set where
  field
    k : Nat
    p : k ≡ 0

record P : Set where
  field
    v : Nat
    ⦃ i ⦄ : C

-- A single pattern variable already makes the context of the pattern
-- lambda larger than the telescope of module M.

module Variable where

  module M (n : Nat) (q : n ≡ 0) where

    instance
      c : C
      c = record { k = n ; p = q }

    f : (b : Bool) → P
    f b = λ where .P.v → 0

  check : C.k (P.i (M.f 0 refl true)) ≡ 0
  check = refl

-- Same with a dot pattern.

module DotPattern where

  data D : Nat → Set where
    d : D 0

  module M (n : Nat) (q : n ≡ 0) where

    instance
      c : C
      c = record { k = n ; p = q }

    f : (m : Nat) (b : Bool) → D m → P
    f .0 b d = λ where .P.v → 0

  check : C.k (P.i (M.f 0 refl 0 true d)) ≡ 0
  check = refl

-- `rewrite` (which is `with` in disguise) reorders the telescope.

module Rewrite where

  record P′ (x : Nat) : Set where
    field
      v : Nat
      ⦃ i ⦄ : C

  module M (n : Nat) (q : n ≡ 0) where

    instance
      c : C
      c = record { k = n ; p = q }

    f : (b : Bool) (m : Nat) → m ≡ 0 → P′ m
    f b m e rewrite e = λ where .P′.v → 0

  check : C.k (P′.i (M.f 0 refl true 0 refl)) ≡ 0
  check = refl

-- A where-function two levels deep: the pattern lambda is created over
-- the telescope of the innermost where-module plus its pattern variable.

module Where where

  module M (n : Nat) (q : n ≡ 0) where

    instance
      c : C
      c = record { k = n ; p = q }

    f : (b : Bool) → P
    f b = g b
      where
        g : Bool → P
        g w = h w
          where
            h : Bool → P
            h u = λ where .P.v → 0

  check : C.k (P.i (M.f 0 refl true)) ≡ 0
  check = refl

-- Nested copattern lambdas: the inner one is created under the binder
-- of the outer one.

module NestedLambdas where

  record R : Set where
    field out : Bool → P

  module M (n : Nat) (q : n ≡ 0) where

    instance
      c : C
      c = record { k = n ; p = q }

    f : R
    f = λ where .R.out b → λ where .P.v → 0

  check : C.k (P.i (R.out (M.f 0 refl) true)) ≡ 0
  check = refl

-- An applied `open` in a `let`: the checkpoint of module N maps its
-- parameters to variables of the clause.

module LetOpen where

  module N (m : Nat) (r : m ≡ 0) where

    instance
      c : C
      c = record { k = m ; p = r }

  module M where

    f : (b : Nat) (e : b ≡ 0) → P
    f b e = let open N b e in λ where .P.v → 0

  check : C.k (P.i (M.f 0 refl)) ≡ 0
  check = refl

-- An applied `open` at the module level.

module AppliedOpen where

  module N (m : Nat) (r : m ≡ 0) where

    instance
      c : C
      c = record { k = m ; p = r }

  module M (n : Nat) (q : n ≡ 0) where

    open N n q

    f : (b : Bool) → P
    f b = λ where .P.v → 0

  check : C.k (P.i (M.f 0 refl true)) ≡ 0
  check = refl

-- The module of a record: its telescope also contains the record value.

module RecordModule where

  record S (n : Nat) (q : n ≡ 0) : Set where

    instance
      c : C
      c = record { k = n ; p = q }

    f : (b : Bool) → P
    f b = λ where .P.v → 0

  s : S 0 refl
  s = record {}

  check : C.k (P.i (S.f s true)) ≡ 0
  check = refl

-- Same for a coinductive record.

module CoinductiveRecordModule where

  record S (n : Nat) (q : n ≡ 0) : Set where
    coinductive
    field force : Bool

    instance
      c : C
      c = record { k = n ; p = q }

    f : (b : Bool) → P
    f b = λ where .P.v → 0

  check : (s : S 0 refl) → C.k (P.i (S.f s true)) ≡ 0
  check s = refl
