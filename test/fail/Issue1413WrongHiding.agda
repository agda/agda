-- Andreas, 2015-05-10  Report wrong hiding for copattern

{-# OPTIONS --copatterns #-}

record ⊤ : Set where

record Foo (A : Set) : Set where
  field
    foo : A

bar : Foo ⊤
Foo.foo {bar} = _

-- Error WAS: Unexpected implicit argument

-- Better error:
-- Wrong hiding used for projection  Foo.foo
-- when checking that the clause Foo.foo {bar} = _ has type Foo ⊤
