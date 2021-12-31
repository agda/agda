-- Andreas, 2021-12-31, issue #5712, reported by Trebor-Huang

-- {-# OPTIONS -v tc.cover.cover:10 #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

nothing : Term → TC ⊤
nothing hole = returnTC _

record Foo : Set1 where
  field
    A : Set
    @(tactic nothing) foo : A → A
open Foo

F : Foo
F .A     = ⊤
F .foo n = _

-- Should succeed.
-- There was an internal error, because the coverage checker did
-- not expand the last clause due to the presence of a tactic (#5358).
-- However, in this case, there is a user argument that forces the
-- expansion.  This is now recognized by the coverage checker.
