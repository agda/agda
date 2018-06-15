-- Andreas, 2018-06-14, issue #2513, surviving shape-irrelevance annotations.

record Foo (A : Set) : Set where
  field
    @shape-irrelevant foo : A

test : ∀ A → Foo A → A
test A = Foo.foo
