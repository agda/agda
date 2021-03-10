module Issue4435-1 where

record ⊤ : Set where

-- Declarations.
data Foo (a : Set) : Set
Bar : {a : Set} → Foo a → Set

-- Definitions.
data Foo a : Set where
  c1 : Foo a
  c2 : (x : Foo a) (y : Bar x → Foo a) → Foo a

Bar c1 = ⊤
Bar (c2 a b) = (x : Bar a) → Bar (b x)
