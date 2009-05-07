-- There was a bug with module application in a let in a
-- parameterised module.
module Issue155 (A : Set) where

module M (Y : Set) where
  postulate F : Set → Set

Foo : Set₁
Foo = let module M′ = M A in (B : Set) → M′.F B

record R : Set₁ where
  open M A
  field
    B : Set
    C : F A
