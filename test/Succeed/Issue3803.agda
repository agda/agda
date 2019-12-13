record Foo : Set where
  field


record A : Set₂ where
  B : Set₁
  B = Set
  field

record C : Set₂ where
  field
  B : Foo
  B = _


record D : Set₂ where
  B : Set₁
  B = Set
  field
  F : Foo
  F = _
