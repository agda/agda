-- Andreas, 2015-05-06 issue reported by Jesper Cockx

-- {-# OPTIONS -v tc.lhs.split:20 #-}

record Foo (A : Set) : Set where
  field
    foo : A

open Foo {{...}} public

record ⊤ : Set where

instance
  Foo⊤ : Foo ⊤
  foo Foo⊤ = {!!}
  -- foo {{Foo⊤}} = {!!}

-- Error WAS:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Rules/LHS/Split.hs:103

-- Better error:
-- Not a valid projection for a copattern: foo
-- when checking that the clause foo Foo⊤ = ? has type Foo ⊤
